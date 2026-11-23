import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Formalism.LocalToGlobal.HermitianForms.TiedTwSymAll
import Formalism.LocalToGlobal.HermitianForms.FramesLemmas
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelCoefficientSpaceRealPoints

noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Forms Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie
open NumberField IsDedekindDomain Matrix GlobalTheory.BigTop GlobalTheory.Mem.R3 GlobalTheory.Core.Rk.Top

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Conj

variable {ι : Type} [Fintype ι] {n : ℕ}

def conjFn (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) : Pol ℂ ι n →ₛₗ[starRingEnd ℂ] (Frames G → ℂ) where
  toFun P := fnOf G s G (MvPolynomial.map (starRingEnd ℂ) P)
  map_add' P Q := by rw [map_add, map_add]
  map_smul' c P := by
    rw [← map_smul]
    congr 1
    simp [MvPolynomial.smul_eq_C_mul]

theorem conjFn_apply {G : ι → Matrix (Fin n) (Fin n) ℂ} (hG : ∀ τ, (G τ).IsHermitian) (s : ι → ℤ) (P : Pol ℂ ι n) (y : Frames G) :
    conjFn G s P y = starRingEnd ℂ ((∏ τ, ((G τ)ᵀ * (y.1 τ).map (starRingEnd ℂ)).det ^ s τ) *
      MvPolynomial.eval (fun x : ι × Fin n × Fin n => ((G x.1)ᵀ * (y.1 x.1).map (starRingEnd ℂ)) x.2.1 x.2.2) P) := by
  have e : ∀ τ, ((G τ)ᵀ * (y.1 τ).map (starRingEnd ℂ)).map (starRingEnd ℂ) = G τ * y.1 τ := fun τ => by
    rw [Matrix.map_mul]
    congr 1
    · exact hG τ
    · ext a b
      simp
  show (∏ τ, (G τ * y.1 τ).det ^ s τ) * MvPolynomial.eval _ (MvPolynomial.map (starRingEnd ℂ) P) = _
  rw [map_mul, map_prod, MvPolynomial.map_eval]
  congr 1
  · refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply, e]
  · congr 2
    funext x
    exact (congrFun (congrFun (e x.1) x.2.1) x.2.2).symm

theorem conjFn_actP {G : ι → Matrix (Fin n) (Fin n) ℂ} (hG : ∀ τ, IsUnit (G τ).det) (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ)
    (hg : ∀ τ, (g τ : Matrix (Fin n) (Fin n) ℂ)ᴴ * G τ * g τ = G τ) (P : Pol ℂ ι n) (y y' : Frames G)
    (h : IsTr (fun τ => (g τ : Matrix (Fin n) (Fin n) ℂ)) y' y) :
    conjFn G (shiftOf lam) (actP lam g P) y = conjFn G (shiftOf lam) P y' := by
  have h1 : ∀ (Q : Pol ℂ ι n) (z : Frames G),
      conjFn G (shiftOf lam) Q z = Formalism.L2.Col.evFr G (shiftOf lam) (starRingEnd ℂ) Q (z.tr G hG) := fun Q z => by
    rw [Formalism.L2.Col.evFr_eq_fnOf, Formalism.L2.Col.fnOf_tr (G' := G) _ 1 G _ _ z fun _ => rfl]
    simp only [Pi.one_apply, Matrix.one_mul]
    rfl
  rw [h1, Formalism.L2.Col.evFr_actP, Formalism.L2.Col.fnOf_tr (G' := G) _ _ (fun τ => G τ * g τ) _ _ y' fun τ => by
    show G τ * y.1 τ = _
    rw [h τ, Matrix.mul_assoc]]
  refine congrArg (fun M => fnOf G (shiftOf lam) M (MvPolynomial.map (starRingEnd ℂ) P) y') (funext fun τ => ?_)
  rw [← Matrix.mul_assoc]
  exact hg τ

theorem conjFn_injective {G : ι → Matrix (Fin n) (Fin n) ℂ} (hG : ∀ τ, IsUnit (G τ).det) (s : ι → ℤ) :
    Function.Injective (conjFn G s) := fun _ _ h =>
  MvPolynomial.map_injective _ (starRingEnd ℂ).injective
    (Formalism.L2.Col.fnOf_injective G s G hG ⟨fun _ => 1, fun _ => by simp⟩ h)

example (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (P : Pol ℂ ι n) : conjFn G s (Complex.I • P) = -Complex.I • conjFn G s P := by
  rw [map_smulₛₗ, Complex.conj_I]

example (G : ι → Matrix (Fin n) (Fin n) ℂ) (τ : ι) (a b : Fin n) (y : Frames G) :
    conjFn G 0 (MvPolynomial.X (τ, a, b)) y = ∑ c, G τ a c * y.1 τ c b := by
  simp [conjFn, fnOf, Matrix.mul_apply]

end Conj

variable {D : D7}

abbrev PtX (D : D7) : Type := Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

theorem reGL_symm_mem {F E : Type} [Field F] [CommRing E] [Algebra F E] (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] {a b : ℕ}
    (h : a = b) (J : Matrix (Fin a) (Fin a) E) {x} (hx : x ∈ Formalism.UG.UPts σ (J.reindex (finCongr h) (finCongr h)) R) :
    (reGL h _).symm x ∈ Formalism.UG.UPts σ J R := by
  subst h
  exact hx

theorem reGL_mem {F E : Type} [Field F] [CommRing E] [Algebra F E] (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] {a b : ℕ}
    (h : a = b) (J : Matrix (Fin a) (Fin a) E) {x} (hx : x ∈ Formalism.UG.UPts σ J R) :
    reGL h _ x ∈ Formalism.UG.UPts σ (J.reindex (finCongr h) (finCongr h)) R := by
  subst h
  exact hx

theorem exists_hasMat (x : PtX D) : ∃ h, HasMat h x.1 := by
  obtain ⟨b, hb⟩ := (GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig D.sp.X'.gram).surjective
    ⟨_, reGL_symm_mem _ _ (rankP D) _ x.2⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig D.sp.X'.gram
  obtain ⟨k, k1, k2⟩ := h2 1 b.1
  refine ⟨⟨k, (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ b.2⟩⟩, k1, fun i j => ?_⟩
  have e2 := (GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig D.sp.X'.gram b).symm.trans (congrArg Subtype.val hb)
  exact congrArg (fun g : GL _ (Lev.EAf D) => g.1 i j) ((congrArg (Formalism.UG.bc (Lev.swapAE D)) k2).trans e2)

theorem finHom_eq {h h' : GA D D.sp.X'} {y} (H : HasMat h y) (H' : HasMat h' y) : finHom D.sp.X' h = finHom D.sp.X' h' :=
  Units.ext (Matrix.ext fun i j =>
    (Algebra.TensorProduct.comm D.host.F _ D.host.E).injective ((H.2 i j).trans (H'.2 i j).symm))

def rowPt (x : PtX D) : Bridge.Gf D.sp.X' := (finHom D.sp.X').rangeRestrict (exists_hasMat x).choose

theorem rowPt_eq {h : GA D D.sp.X'} {x : PtX D} (H : HasMat h x.1) : (finHom D.sp.X').rangeRestrict h = rowPt x :=
  Subtype.ext (finHom_eq H (exists_hasMat x).choose_spec)

theorem rowPt_apply (x : PtX D) (i j) :
    Lev.swapAE D ((rowPt x).1.1 i j) = x.1.1 (finCongr (rankP D) i) (finCongr (rankP D) j) := (exists_hasMat x).choose_spec.2 i j

theorem eq_rowPt {g : Bridge.Gf D.sp.X'} {x : PtX D}
    (H : ∀ i j, Lev.swapAE D (g.1.1 i j) = x.1.1 (finCongr (rankP D) i) (finCongr (rankP D) j)) : g = rowPt x :=
  Subtype.ext (Units.ext (Matrix.ext fun i j =>
    (Algebra.TensorProduct.comm D.host.F _ D.host.E).injective ((H i j).trans (rowPt_apply x i j).symm)))

theorem rowPt_bijective : Function.Bijective (rowPt (D := D)) := by
  refine ⟨fun x x' h => Subtype.ext (Units.ext (Matrix.ext fun i j => ?_)), ?_⟩
  · have h1 := rowPt_apply x ((finCongr (rankP D)).symm i) ((finCongr (rankP D)).symm j)
    rw [h, rowPt_apply] at h1
    exact h1.symm
  · rintro ⟨_, κ, rfl⟩
    obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig D.sp.X'.gram
    have := (GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig D.sp.X'.gram (π κ)).2
    rw [GlobalTheory.Mass.coe_swapPts, hπ κ] at this
    exact ⟨⟨_, reGL_mem _ _ (rankP D) _ this⟩, (eq_rowPt fun _ _ => rfl).symm⟩

abbrev lamX (D : D7) : D.what₂.Tau → DomWeight D.sp.X'.rank := fun τ => Bridge.lamRdef (Ptw D) τ

def conjVal (D : D7) : Pol ℂ D.what₂.Tau D.sp.X'.rank →ₛₗ[starRingEnd ℂ] (FrP D → ℂ) :=
  (conjFn (gramC (gramP D) (embT D)) (shiftOf (lamX D))).comp
    (MvPolynomial.rename (Prod.map id (Prod.map (Fin.cast (rankP D)) (Fin.cast (rankP D))))).toLinearMap

def LevIs {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (S : StepLevel D.host.F D.host.E (sigD D) (gramP D) 1 D.R.f bad)
    (J : Set (GA D D.sp.X')) (χ : GA D D.sp.X' → ℂ) : Prop :=
  (∀ h, h ∈ J ↔ ∃ κ : S.U, HasMat h κ.1) ∧ ∀ h (κ : S.U), HasMat h κ.1 → χ h = star ((S.chi κ : ℂˣ) : ℂ)

theorem levIs_iff_topLev {u : D.what₂.Word} (K : ClsPTied u) (J : Set (GA D D.sp.X')) (χ : GA D D.sp.X' → ℂ) :
    LevIs K.lev J χ ↔ TopLev K J χ := Iff.rfl

theorem adFun_ext {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Fintype ι] {σ : E →ₐ[F] E} {n T f : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {bad : Set (HeightOneSpectrum (𝓞 F))} {S : StepLevel F E σ J T f bad} {emb : ι → E →+* ℂ}
    {cl : Type} {y : cl → Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)} (hy : Function.Surjective fun c => (Quotient.mk'' (y c) : Cls S))
    {g g'} (hg : g ∈ AdFun S emb) (hg' : g' ∈ AdFun S emb) (h : ∀ c, g (y c) = g' (y c)) : g = g' := by
  funext x s
  obtain ⟨c, hc⟩ := hy (Quotient.mk'' x)
  obtain ⟨a, ha, k, hk, e⟩ := (DoubleCoset.eq _ _ _ _).1 hc
  obtain ⟨γ, hγ, ha⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 ha)
  obtain ⟨s', hs⟩ := exists_isTr' emb γ s
  have e' : x.1 = Formalism.UG.bc (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * k.1 := by
    rw [ha]
    exact congrArg Subtype.val e
  exact (hg γ hγ (y c) x ⟨k.1, hk⟩ e' s s' hs).trans
    ((congrArg (fun z => _ * z s') (h c)).trans (hg' γ hγ (y c) x ⟨k.1, hk⟩ e' s s' hs).symm)

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def IsCoord (co : R.cX.W →ₗ[ℂ] Pol ℂ D.what₂.Tau D.sp.X'.rank) : Prop :=
  ∃ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (lamX D)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L ∧
    ∀ v, co (c0R v) = MvPolynomial.map D.what₂.embLL v.1

def conjForm (co : R.cX.W →ₗ[ℂ] Pol ℂ D.what₂.Tau D.sp.X'.rank) (t : T) (f : A.fam.amb.FR t) : PtX D → FrP D → ℂ :=
  fun x => conjVal D (co (R.B.jR t f (rowPt x)))

variable {R}

theorem exists_isCoord (h : R.fam_tie) : ∃ co, IsCoord R co := by
  obtain ⟨gram, c₀, c₁, ht⟩ := h
  obtain ⟨e, he⟩ := GlobalTheory.CoefReal.exists_scalarExt D.what₂.embLL _ c₀ ht.mapR.2.1 ht.mapR.2.2
  refine ⟨(VV ℂ (lamX D)).subtype ∘ₗ e.symm.toLinearMap, gram, c₀, c₁, ht, fun v => ?_⟩
  show (e.symm (c₀ v)).1 = _
  rw [← he, LinearEquiv.symm_apply_apply, GlobalTheory.CoefModel.mapVV_coe]

theorem IsCoord.exists_equiv {co} (h : IsCoord R co) : ∃ e : VV ℂ (lamX D) ≃ₗ[ℂ] R.cX.W, ∀ v, co (e v) = v.1 := by
  obtain ⟨gram, c₀, c₁, ht, hc⟩ := h
  obtain ⟨e, he⟩ := GlobalTheory.CoefReal.exists_scalarExt D.what₂.embLL _ c₀ ht.mapR.2.1 ht.mapR.2.2
  have : co ∘ₗ e.toLinearMap = (VV ℂ (lamX D)).subtype :=
    LinearMap.ext_on_range (GlobalTheory.CoefModel.span_mapVV D.what₂.embLL (lamX D)) fun i => by
      show co (e _) = _
      rw [he, hc]
      exact (GlobalTheory.CoefModel.mapVV_coe _ _ _).symm
  exact ⟨e, LinearMap.congr_fun this⟩

theorem IsCoord.injective {co} (h : IsCoord R co) : Function.Injective co := fun a b hab => by
  obtain ⟨e, he⟩ := h.exists_equiv
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [he, he] at hab
  rw [Subtype.ext hab]

theorem conjForm_eq_model (hj : R.models_jX) (co) (t : T) (f : A.fam.amb.FR t) (x : PtX D) :
    conjForm R co t f x = conjVal D (co ((R.HX t).e (R.jX t f) (rowPt x))) := by
  rw [hj]
  rfl

end Real

theorem strictAnti_unique {N : ℕ} {S : Finset ℚ} (hS : S.card ≤ N) {c c' : Fin N → ℚ} (hc : StrictAnti c) (hc' : StrictAnti c')
    (m : ∀ i, c i ∈ S) (m' : ∀ i, c' i ∈ S) : c = c' := by
  have h1 : S.card = N := le_antisymm hS (by
    simpa using Finset.card_le_card_of_injOn (s := Finset.univ) c (fun i _ => m i) hc.injective.injOn)
  have k : ∀ {c : Fin N → ℚ}, StrictAnti c → (∀ i, c i ∈ S) → (fun i => c (Fin.rev i)) = S.orderEmbOfFin h1 := fun hc m =>
    Finset.orderEmbOfFin_unique h1 (fun _ => m _) fun _ _ h => hc (Fin.rev_lt_rev.2 h)
  funext i
  simpa using congrFun ((k hc m).trans (k hc' m').symm) (Fin.rev i)

theorem shW_eq_lamX (u : D.what₂.Word) (τ : D.what₂.Tau) (sg : DomWeight (D.R.N D.R.m - 1))
    (h : ∀ i, (sg.w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i) (a : Fin D.sp.X'.rank) :
    (shW sg ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ)).w (Fin.cast (rankP D) a) = (lamX D τ).w a := by
  obtain ⟨hcard, c, hc, hmem, hw⟩ := GlobalTheory.ForcedWeights.lamRForced D τ
  rw [GlobalTheory.ForcedWeights.dpar_eq] at hcard hmem
  have hdiv : (((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ) : ℚ) = (D.R.m : ℚ) * ((D.R.t : ℚ) + 1) / 2 := by
    obtain ⟨b, hb⟩ := D.R.m_even
    rw [show D.R.m * (D.R.t + 1) / 2 = b * (D.R.t + 1) by rw [hb, ← two_mul, mul_assoc, Nat.mul_div_cancel_left _ two_pos], hb]
    push_cast
    ring
  have hrho : ∀ a : Fin D.sp.X'.rank, rhoVec (D.R.N D.R.m - 1) (Fin.cast (rankP D) a) = rhoVec _ a := fun a => by
    show (((D.R.N D.R.m - 1 : ℕ) : ℚ) - 1) / 2 - ((a : ℕ) : ℚ) = ((D.sp.X'.rank : ℚ) - 1) / 2 - ((a : ℕ) : ℚ)
    exact congrArg (fun n : ℕ => ((n : ℚ) - 1) / 2 - ((a : ℕ) : ℚ)) (rankP D).symm
  let c' : Fin D.sp.X'.rank → ℚ := fun a => sgHC D.R (D.hcW u τ) a - (D.R.m : ℚ) * ((D.R.t : ℚ) + 1) / 2
  have e' : ∀ a, c' a = (sg.w (Fin.cast (rankP D) a) : ℚ) + rhoVec _ a - (D.R.m : ℚ) * ((D.R.t : ℚ) + 1) / 2 := fun a => by
    rw [h, hrho]
    simp [c']
  have hc' : StrictAnti c' := fun a b hab => by
    have h1 : (sg.w (Fin.cast (rankP D) b) : ℚ) ≤ sg.w (Fin.cast (rankP D) a) := by exact_mod_cast sg.anti hab.le
    have h2 : ((a : ℕ) : ℚ) < (b : ℕ) := by exact_mod_cast hab
    rw [e', e']
    unfold rhoVec
    linarith
  have hm' : ∀ a, ∃ x, GlobalTheory.ForcedWeights.entry (D.hc τ) x = c' a := fun a => by
    have ha : (a : ℕ) < D.R.N D.R.m - 1 := rankP D ▸ a.2
    simp only [c', sgHC, D.hcW_v, D.hcW_b, D.hcW_e, add_sub_cancel_left]
    split_ifs with h1 h2 h3
    · exact ⟨.inl _, rfl⟩
    · exact ⟨.inr (.inl _), rfl⟩
    · have := Nat.mod_lt ((a : ℕ) - (D.R.k - 1)) (Nat.add_one_pos D.R.t)
      refine ⟨.inr (.inr (⟨_, h2⟩, ⟨((a : ℕ) - (D.R.k - 1)) % (D.R.t + 1) - 1, by omega⟩)), ?_⟩
      simp only [GlobalTheory.ForcedWeights.entry]
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    · refine absurd ((Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).2 ?_) h2
      have := D.R.m_add_three_le_k
      unfold Ranks.N at ha
      rw [Nat.succ_eq_add_one]
      omega
  have e : c = c' := strictAnti_unique (S := Finset.univ.image (GlobalTheory.ForcedWeights.entry (D.hc τ)))
    (by
      rw [← hcard, Finset.card_image_of_injective _ (GlobalTheory.ForcedWeights.entry_injective _),
        Finset.card_image_of_injective _ fun x y hh => GlobalTheory.ForcedWeights.entry_injective _ (Prod.ext_iff.1 hh).1]) hc hc'
    (fun i => by
      obtain ⟨s, hs⟩ := hmem i
      obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hs
      exact Finset.mem_image.2 ⟨x, Finset.mem_univ _, (Prod.ext_iff.1 hx).1⟩)
    fun i => let ⟨x, hx⟩ := hm' i; Finset.mem_image.2 ⟨x, Finset.mem_univ _, hx⟩
  have : (((shW sg ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ)).w (Fin.cast (rankP D) a) : ℤ) : ℚ) = ((lamX D τ).w a : ℚ) := by
    rw [hw, e, e']
    show ((sg.w _ - _ : ℤ) : ℚ) = _
    rw [Int.cast_sub, hdiv]
    ring
  exact_mod_cast this

theorem sgT_eq_lamX {u : D.what₂.Word} {K : ClsPTied u} (V : ValPTied u K) (τ : D.what₂.Tau) (a : Fin D.sp.X'.rank) :
    (sgT u τ).w (Fin.cast (rankP D) a) = (lamX D τ).w a := shW_eq_lamX u τ _ (V.sg τ) a

theorem shiftOf_sgT {u : D.what₂.Word} {K : ClsPTied u} (V : ValPTied u K) : shiftOf (sgT u) = shiftOf (lamX D) := funext fun τ => by
  have h0 : 0 < D.R.N D.R.m - 1 := by
    have := D.R.m_add_three_le_k
    have := k_le_N D.R D.R.m
    omega
  have h1 : 0 < D.sp.X'.rank := rankP D ▸ h0
  unfold shiftOf DomWeight.detShift
  rw [dif_pos h0, dif_pos h1, ← sgT_eq_lamX V τ]
  exact congrArg _ (Fin.ext (congrArg (· - 1) (rankP D).symm))

section Point

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

abbrev Coord : Type := p.R.cX.W →ₗ[ℂ] Pol ℂ D.what₂.Tau D.sp.X'.rank

abbrev rowDat (t : p.P.T) : LevDat D.host.E ℂ D.sp.X'.rank := datXP p.R.toRealDat t (p.R.toRealDat.levR p.F.lv2 true)

def rowConj (co : Coord p) (t : p.P.T) (x : Fin (rDim D p.P.A3.A p.P.Ps p.P.ψs t) → D.what₂.LL) : PtX D → FrP D → ℂ :=
  conjForm p.R.toRealDat co t (rowForm p.P.A3.A p.P.Ps p.P.ψs t x)

def JoinAt (co : Coord p) (t : p.P.T) {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) (gramP D) 1 D.R.f bad) {cl : Type} (y : cl → PtX D)
    (rd : D.what₂.Amb (p.P.I.tup t) → cl → FrP D → ℂ) : Prop :=
  LevIs S (levS _ p.R.βX (rowDat p t)) (Lev.levChi _ p.R.βX (rowDat p t)) ∧ ∀ x c, rd (p.P.I.jA t x) c = rowConj p co t x (y c)

variable (Cs : ColsTiedSym D) (tw : SymmetricTwistedColumnsAtPrimes p.Tp Cs ex.tw)

def MtJoinBy (co : Coord p) (e₀ : ∀ u, (D.mem u).P.Mt ≃ₗ[ℂ] D.what₂.Amb D.what₂.mu0)
    (e : ∀ u μ, (D.PTw u μ).Mt ≃ₗ[ℂ] D.what₂.Amb μ) : Prop :=
  (∀ u t (h : p.P.I.tup t = D.what₂.mu0), JoinAt p co t (Cs.forms u).clsP.lev (Cs.forms u).clsP.y fun F =>
    (Cs.forms u).valP.eW ((Cs.forms u).jM ((e₀ u).symm (Eq.rec (motive := fun ν _ => D.what₂.Amb ν) F h)))) ∧
  ∀ u t, Used0 D (p.P.I.tup t) → ∀ h : p.P.I.tup t ≠ D.what₂.mu0,
    JoinAt p co t (tw.pt.cls u _ h).lev (tw.pt.cls u _ h).y fun F => (tw.pt.val u _ h).eW (tw.ptE.jM u _ ((e u _).symm F))

def MtJoin : Prop := ∃ co : Coord p, IsCoord p.R.toRealDat co ∧ MtJoinBy p Cs tw co D.eMt D.eMtTw

theorem exists_coord : ∃ co : Coord p, IsCoord p.R.toRealDat co := exists_isCoord p.charW.base.fam.tie

include p in

theorem gramP_eq_one : gramP D = 1 := by
  refine Matrix.ext fun i j => (p.stdX.1 _ _).trans ?_
  simp [Matrix.one_apply]

include p in

theorem conjVal_eq {u : D.what₂.Word} {K : ClsPTied u} (V : ValPTied u K) (P : Pol ℂ D.what₂.Tau D.sp.X'.rank) :
    conjVal D P = fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map (starRingEnd ℂ)
      (MvPolynomial.rename (Prod.map id (Prod.map (Fin.cast (rankP D)) (Fin.cast (rankP D)))) P)) := by
  have e : gramC (gramP D) (embT D) = 1 := funext fun τ => by
    show (gramP D).map _ = 1
    rw [gramP_eq_one p, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [shiftOf_sgT V]
  exact congrArg (fun M => fnOf (gramC (gramP D) (embT D)) (shiftOf (lamX D)) M _) e

include p in

theorem conjVal_injective : Function.Injective (conjVal D) :=
  (conjFn_injective (fun τ => by
    show IsUnit ((gramP D).map _).det
    rw [gramP_eq_one p, Matrix.map_one _ (map_zero _) (map_one _), det_one]
    exact isUnit_one) _).comp
    (MvPolynomial.rename_injective _ (Function.injective_id.prodMap ((Fin.cast_injective _).prodMap (Fin.cast_injective _))))

theorem span_jA (t : p.P.T) {μ : D.what₂.Tup} (h : p.P.I.tup t = μ) : Submodule.span ℂ (Set.range fun i =>
    (Eq.rec (motive := fun ν _ => D.what₂.Amb ν) (p.P.I.jA t (Pi.single i 1)) h : D.what₂.Amb μ)) = ⊤ := by
  subst h
  exact (p.P.div.sharp.forms t).span

variable {p Cs tw} {co : Coord p} {e₀ e₀' : ∀ u, (D.mem u).P.Mt ≃ₗ[ℂ] D.what₂.Amb D.what₂.mu0}
  {e e' : ∀ u μ, (D.PTw u μ).Mt ≃ₗ[ℂ] D.what₂.Amb μ}

theorem MtJoinBy.jM_eq (h : MtJoinBy p Cs tw co e₀ e) (h' : MtJoinBy p Cs tw co e₀' e') (u : D.what₂.Word) (F : D.what₂.Amb D.what₂.mu0) :
    (Cs.forms u).jM ((e₀ u).symm F) = (Cs.forms u).jM ((e₀' u).symm F) := by
  have ht := p.tupTie _ (Or.inl rfl)
  exact LinearMap.congr_fun (LinearMap.ext_on_range (f := (Cs.forms u).jM.comp (e₀ u).symm.toLinearMap)
    (g := (Cs.forms u).jM.comp (e₀' u).symm.toLinearMap) (span_jA p _ ht) fun i =>
      (Cs.forms u).valP.eW.injective (funext fun c => ((h.1 u _ ht).2 _ c).trans ((h'.1 u _ ht).2 _ c).symm)) F

theorem MtJoinBy.jM_eq_tw (h : MtJoinBy p Cs tw co e₀ e) (h' : MtJoinBy p Cs tw co e₀' e') (u : D.what₂.Word) {μ : D.what₂.Tup}
    (hu : Used0 D μ) (hμ : μ ≠ D.what₂.mu0) (F : D.what₂.Amb μ) : tw.ptE.jM u μ ((e u μ).symm F) = tw.ptE.jM u μ ((e' u μ).symm F) := by
  obtain ⟨t, rfl⟩ : ∃ t, p.P.I.tup t = μ := ⟨_, p.tupTie μ hu⟩
  exact LinearMap.congr_fun (LinearMap.ext_on_range (f := (tw.ptE.jM u _).comp (e u _).symm.toLinearMap)
    (g := (tw.ptE.jM u _).comp (e' u _).symm.toLinearMap) (span_jA p t rfl) fun i =>
      (tw.pt.val u _ hμ).eW.injective (funext fun c => ((h.2 u t hu hμ).2 _ c).trans ((h'.2 u t hu hμ).2 _ c).symm)) F

theorem jM_injective (H : Formalism.L2.Rows.EMtTied D Cs tw) (u : D.what₂.Word) : Function.Injective (Cs.forms u).jM :=
  (injective_iff_map_eq_zero _).2 fun F hF => (D.eMt u).map_eq_zero_iff.1 (inner_self_eq_zero.1 (by
    rw [H.mu0 u F F, hF, map_zero]))

theorem jM_injective_tw (H : Formalism.L2.Rows.EMtTied D Cs tw) (u : D.what₂.Word) {μ : D.what₂.Tup} (hμ : μ ≠ D.what₂.mu0) :
    Function.Injective (tw.ptE.jM u μ) :=
  (injective_iff_map_eq_zero _).2 fun F hF => (D.eMtTw u μ).map_eq_zero_iff.1 (inner_self_eq_zero.1 (by
    rw [H.tw u μ hμ F F, hF, map_zero]))

theorem MtJoinBy.joinEquiv_eq_at_reference (h : MtJoinBy p Cs tw co e₀ e) (h' : MtJoinBy p Cs tw co e₀' e') {u : D.what₂.Word}
    (hj : Function.Injective (Cs.forms u).jM) : e₀ u = e₀' u :=
  LinearEquiv.symm_bijective.injective (LinearEquiv.ext fun F => hj (h.jM_eq h' u F))

theorem MtJoinBy.eq_tw (h : MtJoinBy p Cs tw co e₀ e) (h' : MtJoinBy p Cs tw co e₀' e') {u : D.what₂.Word} {μ : D.what₂.Tup}
    (hu : Used0 D μ) (hμ : μ ≠ D.what₂.mu0) (hj : Function.Injective (tw.ptE.jM u μ)) : e u μ = e' u μ :=
  LinearEquiv.symm_bijective.injective (LinearEquiv.ext fun F => hj (h.jM_eq_tw h' u hu hμ F))

theorem eq_one_of_smul {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] [Nontrivial N] (f : M ≃ₗ[ℂ] N) {c : ℂ}
    (h : ∀ x, f x = c • f x) : c = 1 := by
  obtain ⟨y, hy⟩ := exists_ne (0 : N)
  have := h (f.symm y)
  rw [f.apply_symm_apply] at this
  exact (smul_left_injective ℂ hy ((one_smul ℂ y).trans this)).symm

theorem MtJoinBy.not_scale (h : MtJoinBy p Cs tw co e₀ e) {u : D.what₂.Word} (hj : Function.Injective (Cs.forms u).jM)
    [Nontrivial (D.what₂.Amb D.what₂.mu0)] {c : ℂ} (hc : c ≠ 1) (hs : ∀ G, e₀' u G = c • e₀ u G) : ¬ MtJoinBy p Cs tw co e₀' e' :=
  fun h' => hc (eq_one_of_smul (e₀ u) fun G => by rw [← hs, h.joinEquiv_eq_at_reference h' hj])

theorem MtJoinBy.not_scale_tw (h : MtJoinBy p Cs tw co e₀ e) {u : D.what₂.Word} {μ : D.what₂.Tup} (hu : Used0 D μ) (hμ : μ ≠ D.what₂.mu0)
    (hj : Function.Injective (tw.ptE.jM u μ)) [Nontrivial (D.what₂.Amb μ)] {c : ℂ} (hc : c ≠ 1) (hs : ∀ G, e' u μ G = c • e u μ G) :
    ¬ MtJoinBy p Cs tw co e₀' e' :=
  fun h' => hc (eq_one_of_smul (e u μ) fun G => by rw [← hs, h.eq_tw h' hu hμ hj])

example (h : MtJoinBy p Cs tw co D.eMt D.eMtTw) (H : Formalism.L2.Rows.EMtTied D Cs tw) (u : D.what₂.Word) [Nontrivial (D.what₂.Amb D.what₂.mu0)]
    (hs : ∀ G, e₀' u G = (-1 : ℂ) • D.eMt u G) : ¬ MtJoinBy p Cs tw co e₀' e' :=
  h.not_scale (jM_injective H u) (by norm_num) hs

example (h : MtJoinBy p Cs tw co D.eMt D.eMtTw) (H : Formalism.L2.Rows.EMtTied D Cs tw) (u : D.what₂.Word) {μ : D.what₂.Tup} (hu : Used0 D μ)
    (hμ : μ ≠ D.what₂.mu0) [Nontrivial (D.what₂.Amb μ)] (hs : ∀ G, e' u μ G = Complex.I • D.eMtTw u μ G) :
    ¬ MtJoinBy p Cs tw co e₀' e' :=
  h.not_scale_tw hu hμ (jM_injective_tw H u hμ) (fun hI => by simpa using congrArg Complex.re hI) hs

theorem MtJoin.topLev (h : MtJoin p Cs tw) (u : D.what₂.Word) (t : p.P.T) (ht : p.P.I.tup t = D.what₂.mu0) :
    TopLev (Cs.forms u).clsP (levS _ p.R.βX (rowDat p t)) (Lev.levChi _ p.R.βX (rowDat p t)) :=
  let ⟨_, _, h⟩ := h
  (h.1 u t ht).1

end Point

end GlobalTheory.EX

end
