import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.OriginChartMultiplication

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionCompare

theorem mulF_mapF {T O : Type} [CommRing T] [CommRing O] (f : T →+* O) {d : ℕ} (F : FGLaw T d)
    (n : ℕ) : mulF (F.mapF f) n = fun i => MvPowerSeries.map f (mulSeries F n i) := by
  induction n with
  | zero => funext i; simp [mulF, mulSeries_zero]
  | succ n ih =>
    funext i
    have h : ∀ q : Fin 2 × Fin d, MvPowerSeries.constantCoeff
        ((![mulSeries F n, pt T d 0] : Fin 2 → Pt T 1 d) q.1 q.2) = 0 := by
      rintro ⟨a, j⟩
      fin_cases a
      · exact constantCoeff_mulSeries F n j
      · simp [pt]
    rw [mulSeries_succ]
    show ev ![mulF (F.mapF f) n, pt O d 0] (MvPowerSeries.map f (F.F i)) =
      MvPowerSeries.map f (ev ![mulSeries F n, pt T d 0] (F.F i))
    unfold ev
    rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero h), ih]
    congr 1
    funext q
    obtain ⟨a, j⟩ := q
    fin_cases a
    · rfl
    · simp [pt]

theorem span_mulF_eq_torsionIdeal {T O : Type} [CommRing T] [CommRing O] (f : T →+* O) {d : ℕ}
    (F : FGLaw T d) (n : ℕ) :
    Ideal.span (Set.range (mulF (F.mapF f) n)) = torsionIdeal f F n := by
  rw [mulF_mapF]; rfl

def quotEquiv {T O : Type} [CommRing T] [CommRing O] (f : T →+* O) {d : ℕ}
    (F : FGLaw T d) (n : ℕ) : QF (F.mapF f) n ≃ₐ[O] TorsionRing f F n :=
  Ideal.quotientEquivAlgOfEq O (span_mulF_eq_torsionIdeal f F n)

section Jets

variable {R : Type} [CommRing R]

theorem algOverHom_comp {A B C : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [CommRing C] [Algebra R C] (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) :
    algOverHom (ψ.comp φ) = algOverHom ψ ≫ algOverHom φ := by
  ext1
  simp only [algOverHom, Over.homMk_left, Over.comp_left, spMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rfl

theorem algOverHom_id {A : Type} [CommRing A] [Algebra R A] :
    algOverHom (AlgHom.id R A) = 𝟙 _ := by
  ext1
  simp only [algOverHom, Over.homMk_left, Over.id_left, spMap]
  exact Spec.map_id _

theorem jet_ext {κ S : Type} [CommRing S] [Algebra R S] {m : ℕ} {φ ψ : JetR R κ m →ₐ[R] S}
    (h : ∀ j, φ (zR m j) = ψ (zR m j)) : φ = ψ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h

def jetRename {κ κ' : Type} (e : κ → κ') (m : ℕ) : JetR R κ m →ₐ[R] JetR R κ' m :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval fun q => zR m (e q))
    (aeval_kill m _ _ (fun q => Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self (e q))))
      (jet_aug_pow κ' m))

theorem jetRename_zR {κ κ' : Type} (e : κ → κ') (m : ℕ) (j : κ) :
    jetRename (R := R) e m (zR m j) = zR m (e j) := by
  exact MvPolynomial.aeval_X _ _

theorem jetRename_comp_of_inverse {κ κ' : Type} (e : κ → κ') (e' : κ' → κ)
    (h : ∀ j, e' (e j) = j) (m : ℕ) :
    (jetRename (R := R) e' m).comp (jetRename e m) = AlgHom.id R _ :=
  jet_ext fun j => by rw [AlgHom.comp_apply, jetRename_zR, jetRename_zR, h]; rfl

theorem psJet_eq_jetOfSeries {n d : ℕ} [Nonempty (Fin n × Fin d)] (m : ℕ) (f : PS R n d) :
    psJet m f = jetOfSeries m f := by
  classical
  unfold psJet jetOfSeries
  rw [Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff']
  intro x hx
  rw [MvPolynomial.coeff_sub, MvPowerSeries.coeff_trunc, MvPowerSeries.coeff_truncTotal _ hx,
    if_pos, sub_self]
  have hle : ∀ q, x q < m + 1 := fun q => lt_of_le_of_lt (Finsupp.le_degree q x) hx
  refine lt_of_le_of_ne (fun q => by simpa using (hle q).le) fun h => ?_
  obtain ⟨q⟩ := ‹Nonempty (Fin n × Fin d)›
  have := hle q
  rw [h] at this
  simp at this

theorem substJ_zR {n d : ℕ} (m : ℕ) (φ : Fin d → PS R n d)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (q : Fin 1 × Fin d) :
    substJ m φ hφ (zR m q) = psJet m (φ q.2) := by
  exact MvPolynomial.aeval_X _ _

theorem jetOfSeries_X {κ : Type} [Finite κ] (m : ℕ) (q : κ) :
    jetOfSeries m (MvPowerSeries.X q : MvPowerSeries κ R) = zR m q := by
  unfold jetOfSeries
  rw [Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff']
  intro x hx
  rw [MvPolynomial.coeff_sub, MvPowerSeries.coeff_truncTotal _ hx, ← MvPolynomial.coe_X,
    MvPolynomial.coeff_coe, sub_self]

theorem jetPt_zR {n d : ℕ} (i : Fin n) (m : ℕ) (q : Fin 1 × Fin d) :
    jetPt (T := R) i m (zR m q) = zR m (i, q.2) := by
  have : Nonempty (Fin n × Fin d) := ⟨(i, q.2)⟩
  unfold jetPt
  rw [substJ_zR, psJet_eq_jetOfSeries, jetOfSeries_X]

theorem substJ_zR' {n d : ℕ} [NeZero n] (m : ℕ) (φ : Fin d → PS R n d)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (q : Fin 1 × Fin d) :
    substJ m φ hφ (zR m q) = jetOfSeries m (φ q.2) := by
  have : Nonempty (Fin n × Fin d) := ⟨(0, q.2)⟩
  rw [substJ_zR, psJet_eq_jetOfSeries]

end Jets

section Charts

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G]

def renameChart {G : Over (Sp R)} {σ σ' : Type} (e : σ → σ')
    (x : ∀ m : ℕ, algOver R (JetR R σ m) ⟶ G) : ∀ m : ℕ, algOver R (JetR R σ' m) ⟶ G :=
  fun m => algOverHom (jetRename e m) ≫ x m

theorem renameChart_renameChart {G : Over (Sp R)} {σ σ' : Type} (e : σ → σ') (e' : σ' → σ)
    (h : ∀ j, e' (e j) = j) (x : ∀ m : ℕ, algOver R (JetR R σ m) ⟶ G) :
    renameChart e' (renameChart e x) = x := by
  funext m
  unfold renameChart
  rw [← Category.assoc, ← algOverHom_comp, jetRename_comp_of_inverse e e' h, algOverHom_id,
    Category.id_comp]

def UniversalJets {σ : Type} (x : ∀ m : ℕ, algOver R (JetR R σ m) ⟶ G) : Prop :=
  (∀ m, algOverHom (jetTruncR R σ m) ≫ x (m + 1) = x m) ∧
  (∀ m, algOverHom (jetZeroR R σ m) ≫ x m = toUnit _ ≫ η[G]) ∧
  (∀ (κ : Type) (m : ℕ) (y : algOver R (JetR R κ m) ⟶ G),
    algOverHom (jetZeroR R κ m) ≫ y = toUnit _ ≫ η[G] →
    ∃! ψ : JetR R σ m →ₐ[R] JetR R κ m,
      (∀ j, jetZeroR R κ m (ψ (zR m j)) = 0) ∧ y = algOverHom ψ ≫ x m)

theorem UniversalJets.rename {σ σ' : Type} (e : σ → σ') (e' : σ' → σ)
    (h : ∀ j, e' (e j) = j) (h' : ∀ j, e (e' j) = j)
    {x : ∀ m : ℕ, algOver R (JetR R σ m) ⟶ G} (hx : UniversalJets G x) :
    UniversalJets G (renameChart e x) := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨fun m => ?_, fun m => ?_, fun κ m y hy => ?_⟩
  · unfold renameChart
    have : (jetTruncR R σ' m).comp (jetRename e (m + 1)) =
        (jetRename e m).comp (jetTruncR R σ m) := jet_ext fun j => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, jetRename_zR]
      exact (jetRename_zR e m j).symm
    rw [← Category.assoc, ← algOverHom_comp, this, algOverHom_comp, Category.assoc, h1]
  · unfold renameChart
    have : (jetZeroR R σ' m).comp (jetRename e m) =
        (jetRename e 0).comp (jetZeroR R σ m) := jet_ext fun j => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, jetRename_zR]
      exact (jetRename_zR e 0 j).symm
    rw [← Category.assoc, ← algOverHom_comp, this, algOverHom_comp, Category.assoc, h2,
      ← Category.assoc, comp_toUnit]
  · obtain ⟨ψ, ⟨hψ0, hψ⟩, huniq⟩ := h3 κ m y hy
    refine ⟨ψ.comp (jetRename e' m), ⟨fun j => ?_, ?_⟩, ?_⟩
    · rw [AlgHom.comp_apply, jetRename_zR]; exact hψ0 _
    · unfold renameChart
      rw [← Category.assoc, ← algOverHom_comp, AlgHom.comp_assoc,
        jetRename_comp_of_inverse e e' h, AlgHom.comp_id]
      exact hψ
    · rintro χ ⟨hχ0, hχ⟩
      have : χ.comp (jetRename e m) = ψ := huniq _ ⟨fun j => by
        rw [AlgHom.comp_apply, jetRename_zR]; exact hχ0 _, by
        rw [algOverHom_comp, Category.assoc]; exact hχ⟩
      rw [← this, AlgHom.comp_assoc, jetRename_comp_of_inverse e' e h', AlgHom.comp_id]

variable {d : ℕ}

def toOne (j : Fin d) : Fin 1 × Fin d := (0, j)

theorem toOne_snd (q : Fin 1 × Fin d) : toOne q.2 = q :=
  Prod.ext (Subsingleton.elim _ _) rfl

def chartEquiv (G : Over (Sp R)) (d : ℕ) :
    (∀ m : ℕ, algOver R (JetR R (Fin 1 × Fin d) m) ⟶ G) ≃
      (∀ m : ℕ, algOver R (JetR R (Fin d) m) ⟶ G) where
  toFun := renameChart Prod.snd
  invFun := renameChart toOne
  left_inv := renameChart_renameChart Prod.snd toOne toOne_snd
  right_inv := renameChart_renameChart toOne Prod.snd fun _ => rfl

theorem law_iff (F : FGLaw R d) (x : ∀ m : ℕ, algOver R (JetR R (Fin 1 × Fin d) m) ⟶ G) (m : ℕ) :
    (algOverHom (substJ m F.F F.const) ≫ x m =
      (algOverHom (jetPt (d := d) (0 : Fin 2) m) ≫ x m) *
        (algOverHom (jetPt (d := d) (1 : Fin 2) m) ≫ x m)) ↔
    ∃ ψ₀ ψ₁ ψ : JetR R (Fin d) m →ₐ[R] JetR R (Fin 2 × Fin d) m,
      (∀ j, ψ₀ (zR m j) = zR m ((0 : Fin 2), j)) ∧ (∀ j, ψ₁ (zR m j) = zR m ((1 : Fin 2), j)) ∧
      (∀ j, ψ (zR m j) = jetOfSeries m (F.F j)) ∧
      lift (algOverHom ψ₀ ≫ chartEquiv G d x m) (algOverHom ψ₁ ≫ chartEquiv G d x m) ≫ μ[G] =
        algOverHom ψ ≫ chartEquiv G d x m := by
  have hc : ∀ ψ : JetR R (Fin d) m →ₐ[R] JetR R (Fin 2 × Fin d) m,
      algOverHom ψ ≫ chartEquiv G d x m = algOverHom (ψ.comp (jetRename Prod.snd m)) ≫ x m :=
    fun ψ => by rw [algOverHom_comp, Category.assoc]; rfl
  have hi : ∀ χ : JetR R (Fin 1 × Fin d) m →ₐ[R] JetR R (Fin 2 × Fin d) m,
      (χ.comp (jetRename toOne m)).comp (jetRename Prod.snd m) = χ := fun χ => by
    rw [AlgHom.comp_assoc, jetRename_comp_of_inverse Prod.snd toOne toOne_snd, AlgHom.comp_id]
  constructor
  · intro h
    refine ⟨(jetPt 0 m).comp (jetRename toOne m), (jetPt 1 m).comp (jetRename toOne m),
      (substJ m F.F F.const).comp (jetRename toOne m), fun j => ?_, fun j => ?_, fun j => ?_, ?_⟩
    · rw [AlgHom.comp_apply, jetRename_zR, jetPt_zR]; rfl
    · rw [AlgHom.comp_apply, jetRename_zR, jetPt_zR]; rfl
    · rw [AlgHom.comp_apply, jetRename_zR, substJ_zR']; rfl
    · rw [hc, hc, hc, hi, hi, hi, h]; rfl
  · rintro ⟨ψ₀, ψ₁, ψ, h0, h1, h2, h⟩
    have e0 : ψ₀.comp (jetRename Prod.snd m) = jetPt 0 m := jet_ext fun q => by
      rw [AlgHom.comp_apply, jetRename_zR, h0, jetPt_zR]
    have e1 : ψ₁.comp (jetRename Prod.snd m) = jetPt 1 m := jet_ext fun q => by
      rw [AlgHom.comp_apply, jetRename_zR, h1, jetPt_zR]
    have e2 : ψ.comp (jetRename Prod.snd m) = substJ m F.F F.const := jet_ext fun q => by
      rw [AlgHom.comp_apply, jetRename_zR, h2, substJ_zR']
    rw [hc, hc, hc, e0, e1, e2] at h
    rw [← h]; rfl

theorem isChartJ_iff (F : FGLaw R d) (x : ∀ m : ℕ, algOver R (JetR R (Fin 1 × Fin d) m) ⟶ G) :
    IsChartJ G F x ↔ IsOriginChart G (chartEquiv G d x) F := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := UniversalJets.rename G Prod.snd toOne toOne_snd (fun _ => rfl)
      (x := x) ⟨h.trunc, h.zero, h.univ⟩
    exact ⟨h1, h2, h3, fun m => (law_iff G F x m).mp (h.law m)⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hx := UniversalJets.rename G toOne Prod.snd (fun _ => rfl) toOne_snd
      (x := chartEquiv G d x) ⟨h1, h2, h3⟩
    have e : renameChart toOne (chartEquiv G d x) = x := (chartEquiv G d).left_inv x
    rw [e] at hx
    exact ⟨hx.1, hx.2.1, hx.2.2, fun m => (law_iff G F x m).mpr (h4 m)⟩

theorem isOriginChart_iff (F : FGLaw R d) (x : ∀ m : ℕ, algOver R (JetR R (Fin d) m) ⟶ G) :
    IsOriginChart G x F ↔ IsChartJ G F ((chartEquiv G d).symm x) := by
  rw [isChartJ_iff, Equiv.apply_symm_apply]

end Charts

end GlobalTheory.TorsionCompare
