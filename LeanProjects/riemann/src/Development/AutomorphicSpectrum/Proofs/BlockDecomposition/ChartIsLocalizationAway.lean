import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterEqBasicOpen
open CrystallineSemistableComparison CrystallineSemistableComparison.Onto

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris
namespace GlobalTheory.CompanionTheory.ChartBijOf
open CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT

theorem one_bij (hL : OneLow) (hR : OneRes) {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] (A : Sy.{1} R ι) (a : ℕ)
    (hD : A.Desc) (hO : A.One a) (P : PM.{0} R ι) (hP : P.Ex)
    (E : ∀ S : Finset ι, S.Nonempty → (P.M S ≃ₗ[R] (A.K S).H a))
    (hE : ∀ (S T : Finset ι) (h : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty) (y : P.M S),
      E T hT (P.res h y) = (A.res h).mapH a (E S hS y))
    (X : Cx.{1} R) (f : Cx.Hom X (A.K ∅) (RingHom.id R)) (hX : ∀ j, j ≠ a → Subsingleton (X.H j))
    (r : P.M ∅ ≃ₗ[R] X.H a)
    (hr : ∀ (S : Finset ι) (hS : S.Nonempty) (y : P.M ∅),
      (A.res (Finset.empty_subset S)).mapH a (f.mapH a (r y)) = E S hS (P.res (Finset.empty_subset S) y)) (n : ℕ) :
    Function.Bijective (f.mapH n) := by
  have ne : ∀ {m : ℕ} (i : Fin (m + 1) → ι), (ent i).Nonempty := fun i => ⟨i 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  let φ : ∀ m, P.cech.X m → (A.coh a).cech.X m := fun m x i => E (ent i) (ne i) (x i)
  let ψ : ∀ m, (A.coh a).cech.X m → P.cech.X m := fun m y i => (E (ent i) (ne i)).symm (y i)
  have hφψ : ∀ m y, φ m (ψ m y) = y := fun m y => funext fun i => LinearEquiv.apply_symm_apply _ _
  have hφ0 : ∀ m x, φ m x = 0 → x = 0 := fun m x hx => funext fun i =>
    (LinearEquiv.map_eq_zero_iff (E (ent i) (ne i))).1 (congrFun hx i)
  have hδ : ∀ m (k : Fin (m + 2)) x, (A.coh a).cech.δ m k (φ m x) = φ (m + 1) (P.cech.δ m k x) := fun m k x => funext fun i =>
    (hE _ _ (ent_comp i k.succAbove) (ne _) (ne _) (x (i ∘ k.succAbove))).symm
  have hd : ∀ m x, (A.coh a).cech.d m (φ m x) = φ (m + 1) (P.cech.d m x) := by
    intro m x
    rw [Cos.d_apply, Cos.d_apply]
    funext i
    simp only [hδ, Finset.sum_apply, Pi.smul_apply, φ, map_sum, map_zsmul]
  have hφ1 : ∀ m x y, φ m (x - y) = φ m x - φ m y := fun m x y => funext fun i => map_sub _ _ _
  obtain ⟨-, hinj, hex, hup⟩ := hP
  have hres : (A.coh a).cech.cx.ResUpTo 1 (LinearMap.ker ((A.coh a).cech.d 0)).subtype := by
    refine ⟨fun x => x.2, fun x hx => ?_, fun y hy => ⟨⟨y, hy⟩, (one_smul R y).symm⟩, fun m y hy => ?_⟩
    · rw [one_smul]; exact Subtype.ext hx
    · have h0 : P.cech.d (m + 1) (ψ (m + 1) y) = 0 := hφ0 _ _ (by
        rw [← hd, hφψ]; exact hy)
      obtain ⟨x, hx⟩ := hup m (ψ (m + 1) y) h0
      refine ⟨φ m x, ?_⟩
      change (A.coh a).cech.d m (φ m x) = _
      rw [hd]
      change φ (m + 1) (P.cech.d m x) = _
      rw [show P.cech.d m x = ψ (m + 1) y from hx.trans (one_smul R _), hφψ, one_smul]
  obtain ⟨hz, -⟩ := hR R ι A a hD hO hres
  obtain ⟨-, hin', hex'⟩ := hL R ι A a hD hO
  by_cases hn : n = a
  · subst hn
    have hg : ∀ y, (A.coh n).aug (f.mapH n (r y)) = φ 0 (P.aug y) := fun y => funext fun i => hr _ (ne i) y
    constructor
    · intro x x' hxx
      obtain ⟨y, rfl⟩ := r.surjective x
      obtain ⟨y', rfl⟩ := r.surjective x'
      have h1 : φ 0 (P.aug (y - y')) = 0 := by
        rw [map_sub, hφ1, ← hg, ← hg, hxx, sub_self]
      have h2 := hinj _ (hφ0 _ _ h1)
      rw [one_smul, sub_eq_zero] at h2
      rw [h2]
    · intro z
      have h0 : P.cech.d 0 (ψ 0 ((A.coh n).aug z)) = 0 := hφ0 _ _ (by
        rw [← hd, hφψ]
        exact (hex' _).2 ⟨z, rfl⟩)
      obtain ⟨y, hy⟩ := hex _ h0
      refine ⟨r y, hin' ?_⟩
      rw [hg, show P.aug y = ψ 0 ((A.coh n).aug z) from hy.trans (one_smul R _), hφψ]
  · haveI := hX n hn
    haveI := hz n hn
    exact ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

section Abstract
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {Q : ObjectProperty C} (hQ : Cosieve Q)

theorem cov_bij (hL : OneLow) (hR : OneRes) {ι : Type} [DecidableEq ι] (U : ι → ObjectProperty C)
    (hD : (covSy F U hQ).Desc) (a : ℕ) (P : PM.{0} R ι) (hP : P.Ex)
    (Wp : Finset ι → ObjectProperty C) (hW : ∀ S, S.Nonempty → capU U S = Wp S)
    (V₀ : ObjectProperty C) (hV : capU U ∅ ≤ V₀) (hZ : ∀ n, Function.Bijective ((RC.res F hQ hV).mapH n))
    (hWV : ∀ S, S.Nonempty → Wp S ≤ V₀) (hWle : ∀ S T, S ⊆ T → S.Nonempty → T.Nonempty → Wp T ≤ Wp S)
    (hOne : ∀ S, S.Nonempty → ∀ j, j ≠ a → Subsingleton ((RC F (Wp S) hQ).H j))
    (E : ∀ S : Finset ι, S.Nonempty → (P.M S ≃ₗ[R] (RC F (Wp S) hQ).H a))
    (hE : ∀ (S T : Finset ι) (h : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty) (y : P.M S),
      E T hT (P.res h y) = (RC.res F hQ (hWle S T h hS hT)).mapH a (E S hS y))
    (X : Cx.{1} R) (m : Cx.Hom X (RC F V₀ hQ) (RingHom.id R)) (hX : ∀ j, j ≠ a → Subsingleton (X.H j))
    (r : P.M ∅ ≃ₗ[R] X.H a)
    (hr : ∀ (S : Finset ι) (hS : S.Nonempty) (y : P.M ∅),
      (RC.res F hQ (hWV S hS)).mapH a (m.mapH a (r y)) = E S hS (P.res (Finset.empty_subset S) y)) (n : ℕ) :
    Function.Bijective (m.mapH n) := by
  have hO : (covSy F U hQ).One a := fun S hS j hj => by
    have := hOne S hS j hj
    exact (castH F hQ (hW S hS).symm j).toEquiv.subsingleton_congr.1 this
  have hb := one_bij hL hR (covSy F U hQ) a hD hO P hP
    (fun S hS => (E S hS).trans (castH F hQ (hW S hS).symm a))
    (fun S T h hS hT y => by
      change castH F hQ (hW T hT).symm a (E T hT (P.res h y)) = (RC.res F hQ _).mapH a (castH F hQ (hW S hS).symm a (E S hS y))
      rw [hE S T h hS hT y, cast_res F hQ (hW S hS).symm (hW T hT).symm (hWle S T h hS hT)])
    X (m.comp (RC.res F hQ hV)) hX r
    (fun S hS y => by
      change (RC.res F hQ _).mapH a ((m.comp (RC.res F hQ hV)).mapH a (r y)) = castH F hQ (hW S hS).symm a (E S hS (P.res _ y))
      rw [← hr S hS y, cast_res' F hQ (hW S hS).symm (hWV S hS) ((hW S hS).le.trans (hWV S hS)), comp_mapH, res_res F hQ hV _ ((hW S hS).le.trans (hWV S hS))]) n
  have hb' : Function.Bijective ((RC.res F hQ hV).mapH n ∘ m.mapH n) :=
    Eq.mp (congrArg Function.Bijective (funext fun x => comp_mapH m (RC.res F hQ hV) n x)) hb
  exact (Function.Bijective.of_comp_iff' (hZ n) _).1 hb'
end Abstract

section Sec
variable {K : Type} [Field K] {Z Y : Scheme.{0}}

def secRes (q : Z ⟶ Spec (CommRingCat.of K)) {V V' : Z.Opens} (h : V' ≤ V) : Sec q V →ₐ[K] Sec q V' :=
  { rs h with
    commutes' := fun x => by
      change (Z.presheaf.map (homOfLE h).op).hom ((q.appLE ⊤ V le_top).hom _) = (q.appLE ⊤ V' le_top).hom _
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map] }

def secPull (q : Z ⟶ Spec (CommRingCat.of K)) (π : Y ⟶ Z) {V : Z.Opens} {D : Y.Opens} (h : D ≤ π ⁻¹ᵁ V) : Sec q V →ₐ[K] Sec (π ≫ q) D :=
  { (π.appLE V D h).hom with
    commutes' := fun x => by
      change (π.appLE V D h).hom ((q.appLE ⊤ V le_top).hom _) = ((π ≫ q).appLE ⊤ D le_top).hom _
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE] }

end Sec

section Chart
variable {K : Type} [Field K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {d : ℕ} {V : Z.Opens}

theorem rs_self {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (f : Γ(X, U)) : rs h f = f := by
  change (X.presheaf.map (homOfLE h).op).hom f = f
  simp

theorem chart_isLocalization_away_alt (c : BChart q i π d V) (S : Finset (Fin d)) (k : Fin d) (D₁ D₂ : Y.Opens) (e₁ : D₁ = c.C k)
    (e₂ : D₂ = Y.basicOpen (∏ j ∈ S, c.u k j)) (h : D₂ ≤ D₁) (hu : D₁ ≤ c.C k) :
    letI : Algebra (Sec (π ≫ q) D₁) (Sec (π ≫ q) D₂) := (secRes (π ≫ q) h).toRingHom.toAlgebra
    IsLocalization.Away (R := Sec (π ≫ q) D₁) (∏ j ∈ S, rs hu (c.u k j)) (Sec (π ≫ q) D₂) := by
  subst e₁ e₂
  simp only [rs_self]
  exact (c.C_aff k).isLocalization_basicOpen (∏ j ∈ S, c.u k j)

theorem chart_loc (c : BChart q i π d V) (S : Finset (Fin d)) (k : Fin d) (hk : k ∈ S) :
    letI : Algebra (Sec (π ≫ q) (({k} : Finset (Fin d)).inf c.C)) (Sec (π ≫ q) (S.inf c.C)) :=
      (secRes (π ≫ q) (Finset.inf_mono (Finset.singleton_subset_iff.2 hk))).toRingHom.toAlgebra
    IsLocalization.Away (R := Sec (π ≫ q) (({k} : Finset (Fin d)).inf c.C))
      (∏ j ∈ S, rs (inf_le_C c (Finset.mem_singleton_self k)) (c.u k j)) (Sec (π ≫ q) (S.inf c.C)) :=
  chart_isLocalization_away_alt c S k _ _ Finset.inf_singleton (inf_eq_basicOpen c hk) _ _

theorem chart_presentation_kernel (c : BChart q i π d V) (k : Fin d) (D : Y.Opens) (e : D = c.C k) (hle : D ≤ π ⁻¹ᵁ V) (hu : D ≤ c.C k) :
    Function.Surjective (MvPolynomial.eval₂Hom (π.appLE V D hle).hom fun j => rs hu (c.u k j)) ∧
    RingHom.ker (MvPolynomial.eval₂Hom (π.appLE V D hle).hom fun j => rs hu (c.u k j)) =
      Ideal.span (insert (MvPolynomial.X k - 1) (Set.range fun j => MvPolynomial.C (c.t j) - MvPolynomial.C (c.t k) * MvPolynomial.X j)) := by
  subst e
  simp only [rs_self]
  exact ⟨c.surj k, c.rel k⟩

theorem chart_pres (c : BChart q i π d V) (k : Fin d) :
    Function.Surjective (MvPolynomial.eval₂Hom (π.appLE V (({k} : Finset (Fin d)).inf c.C)
        (inf_le_pre c (Finset.singleton_nonempty k))).hom fun j => rs (inf_le_C c (Finset.mem_singleton_self k)) (c.u k j)) ∧
    RingHom.ker (MvPolynomial.eval₂Hom (π.appLE V (({k} : Finset (Fin d)).inf c.C)
        (inf_le_pre c (Finset.singleton_nonempty k))).hom fun j => rs (inf_le_C c (Finset.mem_singleton_self k)) (c.u k j)) =
      Ideal.span (insert (MvPolynomial.X k - 1) (Set.range fun j => MvPolynomial.C (c.t j) - MvPolynomial.C (c.t k) * MvPolynomial.X j)) :=
  chart_presentation_kernel c k _ Finset.inf_singleton _ _

theorem chart_alt_alt (c : BChart q i π d V) (S : Finset (Fin d)) (k : Fin d) (hk : k ∈ S) (j : Fin d) :
    (π.appLE V (S.inf c.C) (inf_le_pre c ⟨k, hk⟩)).hom (c.t j) =
      (π.appLE V (S.inf c.C) (inf_le_pre c ⟨k, hk⟩)).hom (c.t k) * rs (inf_le_C c hk) (c.u k j) := by
  have hm : (MvPolynomial.C (c.t j) - MvPolynomial.C (c.t k) * MvPolynomial.X j : MvPolynomial (Fin d) Γ(Z, V)) ∈
      RingHom.ker (MvPolynomial.eval₂Hom (π.appLE V (c.C k) (c.C_le k)).hom (c.u k)) := by
    rw [c.rel k]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩)
  rw [RingHom.mem_ker] at hm
  simp only [map_sub, map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X] at hm
  have hrs : ∀ x, rs (inf_le_C c hk) ((π.appLE V (c.C k) (c.C_le k)).hom x) = (π.appLE V (S.inf c.C) (inf_le_pre c ⟨k, hk⟩)).hom x := by
    intro x
    change (Y.presheaf.map (homOfLE _).op).hom ((π.appLE V _ _).hom x) = (π.appLE V _ _).hom x
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  rw [← hrs, ← hrs, ← map_mul]
  exact congrArg _ (sub_eq_zero.1 hm)
end Chart

theorem away_of_equiv {R R' S S' : Type} [CommRing R] [CommRing R'] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R' S']
    (e₁ : R ≃+* R') (e₂ : S ≃+* S') (h : ∀ x, e₂ (algebraMap R S x) = algebraMap R' S' (e₁ x)) (x : R)
    (hx : IsLocalization.Away (e₁ x) S') : IsLocalization.Away x S := by
  haveI := hx
  constructor; constructor
  · rintro ⟨_, n, rfl⟩
    refine (isUnit_map_iff e₂ _).1 ?_
    rw [h]
    have := IsLocalization.map_units (M := Submonoid.powers (e₁ x)) S' ⟨e₁ x ^ n, n, rfl⟩
    simpa using this
  · intro z
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (e₁ x)) (e₂ z)
    refine ⟨⟨e₁.symm a, ⟨x ^ n, n, rfl⟩⟩, e₂.injective ?_⟩
    simp only [map_mul, h, RingEquiv.apply_symm_apply, map_pow] at hz ⊢
    exact hz
  · intro a b
    have h1 : algebraMap R S a = algebraMap R S b ↔ algebraMap R' S' (e₁ a) = algebraMap R' S' (e₁ b) := by
      rw [← h, ← h]
      exact e₂.injective.eq_iff.symm
    rw [h1, IsLocalization.eq_iff_exists (Submonoid.powers (e₁ x)) S']
    rintro ⟨⟨_, n, rfl⟩, hc⟩
    refine ⟨⟨x ^ n, n, rfl⟩, e₁.injective ?_⟩
    simpa using hc

def eqvOf {K : Type} [CommRing K] {X X' : CommAlgCat.{0} K} (e : X = X') : X ≃ₐ[K] X' := by
  subst e; exact AlgEquiv.refl

theorem glue_rings {K : Type} [CommRing K] {ι : Type} (A : Type) [CommRing A] [Algebra K A] (B : Finset ι → Type)
    [∀ S, CommRing (B S)] [∀ S, Algebra K (B S)] (ρ : ∀ {S T : Finset ι}, S ⊆ T → (B S →ₐ[K] B T))
    (ρ_id : ∀ (S : Finset ι) (h : S ⊆ S) y, ρ h y = y)
    (ρ_comp : ∀ {S T U : Finset ι} (h : S ⊆ T) (h' : T ⊆ U) y, ρ h' (ρ h y) = ρ (h.trans h') y)
    (τ : ∀ S : Finset ι, S.Nonempty → (A →ₐ[K] B S))
    (hτ : ∀ {S T : Finset ι} (h : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty) x, ρ h (τ S hS x) = τ T hT x) :
    ∃ (R : Finset ι → CommAlgCat.{0} K) (res : ∀ {S T : Finset ι}, S ⊆ T → (R S →ₐ[K] R T)) (base : R ∅ ≃ₐ[K] A)
      (b : ∀ S : Finset ι, S.Nonempty → (R S ≃ₐ[K] B S)),
      (∀ (S : Finset ι) (h : S ⊆ S) y, res h y = y) ∧
      (∀ {S T U : Finset ι} (h : S ⊆ T) (h' : T ⊆ U) y, res h' (res h y) = res (h.trans h') y) ∧
      (∀ (S T : Finset ι) (h : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty) y, b T hT (res h y) = ρ h (b S hS y)) ∧
      (∀ (T : Finset ι) (hT : T.Nonempty) g, b T hT (res (Finset.empty_subset T) (base.symm g)) = τ T hT g) := by
  classical
  let Rf : Finset ι → CommAlgCat.{0} K := fun S => if S.Nonempty then CommAlgCat.of K (B S) else CommAlgCat.of K A
  let b : ∀ S : Finset ι, S.Nonempty → (Rf S ≃ₐ[K] B S) := fun S hS => eqvOf (if_pos hS)
  let bA : ∀ S : Finset ι, ¬ S.Nonempty → (Rf S ≃ₐ[K] A) := fun S hS => eqvOf (if_neg hS)
  let res : ∀ {S T : Finset ι}, S ⊆ T → (Rf S →ₐ[K] Rf T) := fun {S T} h =>
    if hS : S.Nonempty then ((b T (hS.mono h)).symm : B T →ₐ[K] Rf T).comp ((ρ h).comp (b S hS : Rf S →ₐ[K] B S))
    else if hT : T.Nonempty then ((b T hT).symm : B T →ₐ[K] Rf T).comp ((τ T hT).comp (bA S hS : Rf S →ₐ[K] A))
    else ((bA T hT).symm : A →ₐ[K] Rf T).comp (bA S hS : Rf S →ₐ[K] A)
  have r1 : ∀ {S T : Finset ι} (h : S ⊆ T) (hS : S.Nonempty) (y : Rf S), res h y = (b T (hS.mono h)).symm (ρ h (b S hS y)) := by
    intro S T h hS y
    simp only [res, dif_pos hS]
    rfl
  have r2 : ∀ {S T : Finset ι} (h : S ⊆ T) (hS : ¬ S.Nonempty) (hT : T.Nonempty) (y : Rf S),
      res h y = (b T hT).symm (τ T hT (bA S hS y)) := by
    intro S T h hS hT y
    simp only [res, dif_neg hS, dif_pos hT]
    rfl
  have r3 : ∀ {S T : Finset ι} (h : S ⊆ T) (hS : ¬ S.Nonempty) (hT : ¬ T.Nonempty) (y : Rf S),
      res h y = (bA T hT).symm (bA S hS y) := by
    intro S T h hS hT y
    simp only [res, dif_neg hS, dif_neg hT]
    rfl
  have h0 : ¬ (∅ : Finset ι).Nonempty := Finset.not_nonempty_empty
  refine ⟨Rf, res, bA ∅ h0, b, ?_, ?_, ?_, ?_⟩
  · intro S h y
    by_cases hS : S.Nonempty
    · rw [r1 h hS, ρ_id, AlgEquiv.symm_apply_apply]
    · rw [r3 h hS hS, AlgEquiv.symm_apply_apply]
  · intro S T U h h' y
    by_cases hS : S.Nonempty
    · rw [r1 h hS, r1 h' (hS.mono h), r1 _ hS, AlgEquiv.apply_symm_apply, ρ_comp]
    by_cases hT : T.Nonempty
    · rw [r2 h hS hT, r1 h' hT, r2 _ hS (hT.mono h'), AlgEquiv.apply_symm_apply, hτ h' hT (hT.mono h')]
    by_cases hU : U.Nonempty
    · rw [r3 h hS hT, r2 h' hT hU, r2 _ hS hU, AlgEquiv.apply_symm_apply]
    · rw [r3 h hS hT, r3 h' hT hU, r3 _ hS hU, AlgEquiv.apply_symm_apply]
  · intro S T h hS hT y
    rw [r1 h hS, AlgEquiv.apply_symm_apply]
  · intro T hT g
    rw [r2 _ h0 hT, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

theorem pres_transport {A R B ι : Type} [CommRing A] [CommRing R] [CommRing B] [Algebra A R] (g : A →+* B) (β : R ≃+* B)
    (hg : ∀ a, β (algebraMap A R a) = g a) (v : ι → R) (w : ι → B) (hw : ∀ j, β (v j) = w j)
    (p : MvPolynomial ι A) : β (MvPolynomial.aeval v p) = MvPolynomial.eval₂Hom g w p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [hg]
  | add p p' hp hp' => simp only [map_add, hp, hp']
  | mul_X p j hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval₂Hom_X', hw]

theorem chart_exists (K : Type) [Field K] (W Z Y : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z)
    (π : Y ⟶ Z) (d : ℕ) (V : Z.Opens) (c : BChart q i π d V) :
    ∃ (C : ChartRings K (Sec q V) c.n d) (b : ∀ S : Finset (Fin d), S.Nonempty → (C.R S ≃ₐ[K] Sec (π ≫ q) (S.inf c.C))),
      (∀ (S T : Finset (Fin d)) (h : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty) (y : C.R S),
        b T hT (C.res h y) = rs (Finset.inf_mono h) (b S hS y)) ∧
      (∀ (T : Finset (Fin d)) (hT : T.Nonempty) (g : Sec q V),
        b T hT (C.res (Finset.empty_subset T) (C.base.symm g)) = (π.appLE V (T.inf c.C) (inf_le_pre c hT)).hom g) ∧
      (∀ j, C.t j = c.t j) := by
  obtain ⟨R, res, base, b, res_id, res_comp, hb1, hb2⟩ := glue_rings (K := K) (Sec q V) (fun S : Finset (Fin d) => Sec (π ≫ q) (S.inf c.C))
    (fun h => secRes (π ≫ q) (Finset.inf_mono h))
    (fun S h y => by
      change (Y.presheaf.map (homOfLE _).op).hom y = y
      simp)
    (fun h h' y => by
      change (Y.presheaf.map (homOfLE _).op).hom ((Y.presheaf.map (homOfLE _).op).hom y) = (Y.presheaf.map (homOfLE _).op).hom y
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl)
    (fun S hS => secPull q π (inf_le_pre c hS))
    (fun h hS hT x => by
      change (Y.presheaf.map (homOfLE _).op).hom ((π.appLE V _ _).hom x) = (π.appLE V _ _).hom x
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map])
  refine ⟨{ x := c.x, t := c.t, etale := c.etale, R := fun S => R S, cr := fun S => inferInstance, alg := fun S => inferInstance,
            res := res, res_id := res_id, res_comp := res_comp, base := base,
            u := fun S k hk j => (b S ⟨k, hk⟩).symm (rs (inf_le_C c hk) (c.u k j)),
            t_eq := ?_, u_res := ?_, chart_surj := ?_, chart_ker := ?_, loc := ?_ }, b, hb1, hb2, fun j => rfl⟩
  · intro S k hk j
    apply (b S ⟨k, hk⟩).injective
    rw [map_mul, hb2, hb2, AlgEquiv.apply_symm_apply]
    exact chart_alt_alt c S k hk j
  · intro S T h k hk j
    apply (b T ⟨k, h hk⟩).injective
    rw [hb1 S T h ⟨k, hk⟩ ⟨k, h hk⟩, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    change (Y.presheaf.map (homOfLE _).op).hom ((Y.presheaf.map (homOfLE _).op).hom _) = (Y.presheaf.map (homOfLE _).op).hom _
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  · intro k
    letI : Algebra (Sec q V) (R {k}) := ((res (Finset.empty_subset {k})).toRingHom.comp base.symm.toRingHom).toAlgebra
    intro y
    have hk : ({k} : Finset (Fin d)).Nonempty := Finset.singleton_nonempty k
    obtain ⟨p, hp⟩ := (chart_pres c k).1 (b {k} hk y)
    refine ⟨p, (b {k} hk).injective ?_⟩
    refine Eq.trans ?_ hp
    exact pres_transport (A := Sec q V) (R := R {k}) (B := Sec (π ≫ q) (({k} : Finset (Fin d)).inf c.C))
      (secPull q π (inf_le_pre c hk)).toRingHom (b {k} hk).toRingEquiv (fun a => hb2 {k} hk a) _ _
      (fun j => AlgEquiv.apply_symm_apply _ _) p
  · intro k
    letI : Algebra (Sec q V) (R {k}) := ((res (Finset.empty_subset {k})).toRingHom.comp base.symm.toRingHom).toAlgebra
    have hk : ({k} : Finset (Fin d)).Nonempty := Finset.singleton_nonempty k
    refine Eq.trans ?_ (chart_pres c k).2
    ext p
    rw [RingHom.mem_ker, RingHom.mem_ker]
    have hp := pres_transport (A := Sec q V) (R := R {k}) (B := Sec (π ≫ q) (({k} : Finset (Fin d)).inf c.C))
      (secPull q π (inf_le_pre c hk)).toRingHom (b {k} hk).toRingEquiv (fun a => hb2 {k} hk a)
      (fun j => (b {k} hk).symm (rs (inf_le_C c (Finset.mem_singleton_self k)) (c.u k j)))
      (fun j => rs (inf_le_C c (Finset.mem_singleton_self k)) (c.u k j)) (fun j => AlgEquiv.apply_symm_apply _ _) p
    refine Iff.trans ?_ (Eq.congr_left hp)
    exact (map_eq_zero_iff _ (b {k} hk).injective).symm
  · intro S k hk
    letI : Algebra (R {k}) (R S) := (res (Finset.singleton_subset_iff.2 hk)).toRingHom.toAlgebra
    have hk1 : ({k} : Finset (Fin d)).Nonempty := Finset.singleton_nonempty k
    have hS : S.Nonempty := ⟨k, hk⟩
    letI : Algebra (Sec (π ≫ q) (({k} : Finset (Fin d)).inf c.C)) (Sec (π ≫ q) (S.inf c.C)) :=
      (secRes (π ≫ q) (Finset.inf_mono (Finset.singleton_subset_iff.2 hk))).toRingHom.toAlgebra
    refine away_of_equiv (S' := Sec (π ≫ q) (S.inf c.C)) (b {k} hk1).toRingEquiv (b S hS).toRingEquiv
      (fun x => hb1 {k} S _ hk1 hS x) _ ?_
    have he : (b {k} hk1).toRingEquiv (∏ j ∈ S, (b {k} hk1).symm (rs (inf_le_C c (Finset.mem_singleton_self k)) (c.u k j))) =
        ∏ j ∈ S, rs (inf_le_C c (Finset.mem_singleton_self k)) (c.u k j) := by
      rw [map_prod]
      exact Finset.prod_congr rfl fun j _ => AlgEquiv.apply_symm_apply _ _
    exact he ▸ chart_loc c S k hk

section Main
set_option maxHeartbeats 4000000 in

theorem chartBij_of : ChartFormsCechExact → SiteLaws → OneLow → OneRes → CovDesc → ZarRel → AffOm → OmNat → OmRes → AffRel → FormLaws →
    ChartLaws → ChartBij := by
  intro hH hS hL hR hC hZ hA hN hOR hAR hF hCL K _ _ W Z Y q i _ π d hd V hc hQ hQ' a h h' n
  obtain ⟨c⟩ := hc
  obtain ⟨C, b, hb1, hb2, ht⟩ := chart_exists K W Z Y q i π d V c
  obtain ⟨hI, hI0⟩ := chart_ideal hCL K W Z Y q i π d V c C b hb2 ht
  obtain ⟨P, eP, hPc, hPEx⟩ := rel_pm hH K (Sec q V) c.n d hd C a
  have hlaws := hCL K W Z Y q i π d V c
  have hloc : ∀ (S : Finset (Fin d)) (hS : S.Nonempty), ∃ e : Om K (Sec (π ≫ q) (S.inf c.C)) a →ₗ[K] HV (π ≫ q) (S.inf c.C) a a,
      IsOm (π ≫ q) (S.inf c.C) a e ∧
      (∀ j, j ≠ a → Subsingleton ((RC (G (π ≫ q) a) (inU (π ≫ q) (S.inf c.C)) hQ').H j)) ∧
      Function.Injective ((incl (G (π ≫ q) a) (inU (π ≫ q) (S.inf c.C)) hQ').mapH a) ∧
      ∃ E : P.M S ≃ₗ[K] (RC (G (π ≫ q) a) (inU (π ≫ q) (S.inf c.C)) hQ').H a,
        ∀ y, (incl (G (π ≫ q) a) (inU (π ≫ q) (S.inf c.C)) hQ').mapH a (E y) =
          e (omMap (b S hS : C.R S →ₐ[K] Sec (π ≫ q) (S.inf c.C)) a (eP S y : Om K (C.R S) a)) := fun S hS => by
    obtain ⟨k, hk⟩ := id hS
    obtain ⟨h1, h2, -, -⟩ := hlaws.2.2.2 k (S.inf c.C) (inf_le_C c hk) (inf_affine c hS)
    exact loc_iso hA hAR K (pullback i π) Y (π ≫ q) (pullback.snd i π) hQ' (S.inf c.C) _ _ h1 h2 a (C.I S) (b S hS) (hI S hS) (eP S)
  choose e he hone hinj E hEe using hloc
  obtain ⟨e0, he0, hone0, hinj0, r, hr0⟩ :=
    loc_iso hA hAR K W Z q i hQ V _ _ hlaws.2.1 hlaws.2.2.1 a (C.I ∅) C.base hI0 (eP ∅)
  obtain ⟨hcos, -, htop, hinf, -⟩ := hS K (pullback i π) Y Y (π ≫ q) (pullback.snd i π) (𝟙 Y)
  have hmono : ∀ D D₀ : Y.Opens, D ≤ D₀ → inU (π ≫ q) D ≤ inU (π ≫ q) D₀ := fun D D₀ hle T hT =>
    ((hinf D D₀ T).1 (by rwa [inf_eq_left.2 hle])).2
  have hall : ∀ (T : Thick (smFun Y (π ≫ q))) (S : Finset (Fin d)), (∀ α ∈ S, inU (π ≫ q) (c.C α) T) → inU (π ≫ q) (S.inf c.C) T := by
    intro T S
    induction S using Finset.induction_on with
    | empty => intro _; simpa using htop T
    | insert j S hj ih =>
      intro hT
      rw [Finset.inf_insert]
      exact (hinf _ _ T).2 ⟨hT j (Finset.mem_insert_self j S), ih fun α hα => hT α (Finset.mem_insert_of_mem hα)⟩
  have hcap : ∀ S : Finset (Fin d), S.Nonempty → capU (fun k => inU (π ≫ q) (c.C k)) S = inU (π ≫ q) (S.inf c.C) := by
    intro S hS
    funext T
    refine propext ⟨fun hT => hall T S hT.2, fun hT => ?_⟩
    obtain ⟨k, hk⟩ := hS
    exact ⟨⟨k, hmono _ _ (inf_le_C c hk) T hT⟩, fun α hα => hmono _ _ (inf_le_C c hα) T hT⟩
  have hV : capU (fun k => inU (π ≫ q) (c.C k)) ∅ ≤ inU (π ≫ q) (π ⁻¹ᵁ V) := fun T hT => by
    obtain ⟨k, hk⟩ := hT.1
    exact hmono _ _ (c.C_le k) T hk
  have hgen : ∀ (U₀ : ObjectProperty (Thick (smFun Y (π ≫ q)))) (e₀ : U₀ = fun T => ∃ α, inU (π ≫ q) (c.C α) T)
      (hle : U₀ ≤ inU (π ≫ q) (π ⁻¹ᵁ V)) (n : ℕ), Function.Bijective ((RC.res (G (π ≫ q) a) hQ' hle).mapH n) := by
    intro U₀ e₀ hle n
    subst e₀
    exact hZ K (pullback i π) Y (π ≫ q) (pullback.snd i π) hQ' (Fin d) (π ⁻¹ᵁ V) c.C
      (le_antisymm (iSup_le c.C_le) c.C_cover) hle a n
  have hZ' := hgen _ (by
    funext T
    exact propext ⟨fun hT => hT.1, fun hT => ⟨hT, fun α hα => absurd hα (Finset.notMem_empty α)⟩⟩) hV
  have hWV : ∀ S : Finset (Fin d), S.Nonempty → inU (π ≫ q) (S.inf c.C) ≤ inU (π ≫ q) (π ⁻¹ᵁ V) :=
    fun S hS => hmono _ _ (inf_le_pre c hS)
  have hWle : ∀ S T : Finset (Fin d), S ⊆ T → S.Nonempty → T.Nonempty → inU (π ≫ q) (T.inf c.C) ≤ inU (π ≫ q) (S.inf c.C) :=
    fun S T h _ _ => hmono _ _ (Finset.inf_mono h)
  refine cov_bij (G (π ≫ q) a) hQ' hL hR (fun k => inU (π ≫ q) (c.C k))
    (hC K (Fin d) _ (G (π ≫ q) a) _ _ hQ' fun k => hcos _) a P hPEx (fun S => inU (π ≫ q) (S.inf c.C)) hcap
    (inU (π ≫ q) (π ⁻¹ᵁ V)) hV hZ' hWV hWle hone E ?_ _ (pullRC π rfl a (U := inU q V) (U' := inU (π ≫ q) (π ⁻¹ᵁ V)) hQ hQ' h h')
    hone0 r ?_ n
  · intro S T hST hS' hT y
    apply hinj T hT
    rw [hEe T hT, incl_res, hEe S hS']
    obtain ⟨φ, hφ, -, hnat⟩ := hOR K Y (π ≫ q) (S.inf c.C) (T.inf c.C) (Finset.inf_mono hST) (hWle S T hST hS' hT)
    have hcomp : φ.comp (b S hS' : C.R S →ₐ[K] Sec (π ≫ q) (S.inf c.C)) =
        (b T hT : C.R T →ₐ[K] Sec (π ≫ q) (T.inf c.C)).comp (C.res hST) := AlgHom.ext fun y => by
      change φ (b S hS' y) = b T hT (C.res hST y)
      rw [hφ, hb1 S T hST hS' hT y]
    rw [hnat a _ _ (he S hS') (he T hT), hPc S T hST y, GlobalTheory.CompanionTheory.SurjectionOntoH4.omMap_comp, GlobalTheory.CompanionTheory.SurjectionOntoH4.omMap_comp, hcomp]
  · intro S hS' y
    apply hinj S hS'
    have h₁ : ∀ T, inU (π ≫ q) (S.inf c.C) T → inU q V ((smS π rfl).G.obj T) := fun T hT => h T (hWV S hS' T hT)
    obtain ⟨φ, hφ, hnat⟩ := hN K Z Y q (π ≫ q) π rfl V (S.inf c.C) (inf_le_pre c hS') h₁
    refine ((incl_pull (i := i) (π := π) a hQ hQ' V (π ⁻¹ᵁ V) (S.inf c.C) (hWV S hS') h h₁ h' (r y)).trans
      ((congrArg _ (hr0 y)).trans (hnat a _ _ he0 (he S hS') _))).trans (Eq.trans ?_ (hEe S hS' _).symm)
    refine congrArg _ ?_
    have hcomp : φ.comp (C.base : C.R ∅ →ₐ[K] Sec q V) =
        (b S hS' : C.R S →ₐ[K] Sec (π ≫ q) (S.inf c.C)).comp (C.res (Finset.empty_subset S)) := AlgHom.ext fun y => by
      change φ (C.base y) = b S hS' (C.res _ y)
      have h2 := hb2 S hS' (C.base y)
      rw [AlgEquiv.symm_apply_apply] at h2
      rw [hφ, h2]
    rw [hPc ∅ S _ y, GlobalTheory.CompanionTheory.SurjectionOntoH4.omMap_comp, GlobalTheory.CompanionTheory.SurjectionOntoH4.omMap_comp, hcomp]
end Main

end GlobalTheory.CompanionTheory.ChartBijOf
