import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelHasJacobianOrder
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ChainRuleAndJacobianCriterion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsOpenImmersionOfExtendsIdOfEtale
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.Ord
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GlobalTheory.SS.OrdMono

section
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}
  {I : Type} [Fintype I] [DecidableEq I]

abbrev IsCoord (M : Model R A) {I : Type} (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U)) : Prop :=
  (MvPolynomial.eval₂Hom (cst M U) t).Etale

abbrev jm (M : Model R A) (D : I → VF A) (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U)) : Γ(A.left, M.j ⁻¹ᵁ U) :=
  jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i))

theorem etale_comp {B C I : Type} [CommRing B] [CommRing C] (c : R →+* B) (t : I → B) (φ : B →+* C)
    (h : (MvPolynomial.eval₂Hom c t).Etale) (hφ : φ.Etale) :
    (MvPolynomial.eval₂Hom (φ.comp c) (fun i => φ (t i))).Etale := by
  rw [← MvPolynomial.comp_eval₂Hom]
  exact RingHom.Etale.stableUnderComposition _ _ h hφ

theorem chain_model (M : Model R A) (D : I → VF A) (U : M.Y.left.Opens) (t t' : I → Γ(M.Y.left, U))
    (h : IsCoord M U t) : ∃ a, jm M D U t' = (M.j.app U).hom a * jm M D U t ∧ (IsUnit a → IsCoord M U t') := by
  obtain ⟨a, h1, h2⟩ := GlobalTheory.EtaleCoordJacobian.chain_rule_and_jacobian_criterion R _ (cst M U) I t t' h
  refine ⟨a, h1 _ (M.j.app U).hom (fun i => ((D i).D _).comp (M.j.app U).hom.toAddMonoidHom)
    (fun i x y => ?_) (fun i r => ?_), h2⟩
  · show (D i).D _ ((M.j.app U).hom (x * y)) = _
    rw [map_mul, (D i).leibniz]; rfl
  · show (D i).D _ ((M.j.app U).hom (cst M U r)) = _
    rw [j_cst, (D i).const]

theorem etale_rs (X : Scheme.{0}) {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U) :
    (rs X h).Etale := by
  have := (𝟙 X : X ⟶ X).etale_appLE hU hV h
  simpa [Scheme.Hom.appLE] using this

theorem coord_rs (M : Model R A) {I : Type} {U V : M.Y.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V ≤ U) {t : I → Γ(M.Y.left, U)} (ht : IsCoord M U t) : IsCoord M V fun i => rs _ h (t i) := by
  have := etale_comp _ t _ ht (etale_rs _ hU hV h)
  have e : (rs _ h).comp (cst M U) = cst M V := RingHom.ext (rs_cst M h)
  rwa [e] at this

theorem rs_jm (M : Model R A) (D : I → VF A) {U V : M.Y.left.Opens} (h : V ≤ U) (t : I → Γ(M.Y.left, U)) :
    rs _ (M.j.preimage_mono h) (jm M D U t) = jm M D V fun i => rs _ h (t i) := by
  rw [jm, rs_jac]; exact congrArg (jac D _) (funext fun i => rs_j M h (t i))

theorem isUnit_of_local (X : Scheme.{0}) (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧ IsUnit (rs X hV f)) : IsUnit f := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx => ?_
  obtain ⟨V, hV, hxV, hu⟩ := h x hx
  have := hu.map (X.presheaf.germ V x hxV).hom
  exact (X.presheaf.germ_res_apply (homOfLE hV) x hxV f).subst this

theorem isUnit_of_dvd_pow {B : Type} [CommRing B] {p s : B} (hp : Prime p) (h0 : p ∈ nonZeroDivisors B)
    (hs : ¬ p ∣ s) (k : ℕ) (h : s ∣ p ^ k) : IsUnit s := by
  induction k with
  | zero => exact isUnit_of_dvd_one (by simpa using h)
  | succ k ih =>
    obtain ⟨b, hb⟩ := h
    obtain ⟨b', rfl⟩ : p ∣ b := (hp.dvd_or_dvd (hb ▸ dvd_pow_self p k.succ_ne_zero)).resolve_left hs
    refine ih ⟨b', ?_⟩
    have : p * (p ^ k - s * b') = 0 := by linear_combination hb
    exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff_left.1 h0) _ this)
end

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Over (Sp K)} {π : R} {I : Type} [Fintype I] [DecidableEq I]

theorem isUnit_jm (M : Model R A) {D : I → VF A} (hD : IsFrame D) {U : M.Y.left.Opens} (hU : IsAffineOpen U)
    {t : I → Γ(M.Y.left, U)} (ht : IsCoord M U t) : IsUnit (jm M D U t) := by
  have := isOpenImmersion_j M
  refine isUnit_of_local _ _ _ fun z hz => ?_
  obtain ⟨U', t', hz', hu⟩ := hD.2 z
  obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := A.left) (U := U' ⊓ M.j ⁻¹ᵁ U) ⟨hz', hz⟩
  have h1 : V ≤ U' := fun _ h => (hle h).1
  have h2 : V ≤ M.j ⁻¹ᵁ U := fun _ h => (hle h).2
  refine ⟨V, h2, hzV, ?_⟩
  have he := etale_comp _ t _ ht (M.j.etale_appLE hU hV h2)
  obtain ⟨a, ha, -⟩ := GlobalTheory.EtaleCoordJacobian.chain_rule_and_jacobian_criterion R _ _ I _ (fun i => rs _ h1 (t' i)) he
  have hb := ha _ (RingHom.id _) (fun i => (D i).D V) (fun i => (D i).leibniz V) (fun i r => by
    have : ((M.j.appLE U V h2).hom.comp (cst M U)) r = cstK A V (algebraMap R K r) := by
      rw [← rs_cstK h2, ← j_cst]; rfl
    rw [this, (D i).const])
  have hc : IsUnit (jac D V fun i => rs _ h1 (t' i)) := by rw [← rs_jac]; exact hu.map _
  rw [jm, rs_jac]
  exact isUnit_of_mul_isUnit_right (show IsUnit (_ * _) from hb.subst hc)

theorem isUnit_cstK (hπ : Irreducible π) (U : A.left.Opens) (n : ℤ) : IsUnit (cstK A U (algebraMap R K π ^ n)) :=
  (IsUnit.mk0 _ (zpow_ne_zero n (by simpa using hπ.ne_zero))).map _

theorem chart (hπ : Irreducible π) (M : Model R A) (hM : M.Irr) {D : I → VF A} (hD : IsFrame D) {n : ℤ}
    (hn : HasOrd M D π n) {U : M.Y.left.Opens} (hU : IsAffineOpen U) (h : ((U : Set M.Y.left) ∩ M.sp).Nonempty)
    {t : I → Γ(M.Y.left, U)} (ht : IsCoord M U t) :
    ∃ s : Γ(M.Y.left, U), IsUnit s ∧ jm M D U t = cstK A _ (algebraMap R K π ^ n) * (M.j.app U).hom s := by
  obtain ⟨s, hs⟩ := hn.1 U t
  refine ⟨s, ?_, hs⟩
  obtain ⟨U₀, t₀, s₀, h₀, hu₀, hs₀⟩ := hn.2
  have hjs : IsUnit ((M.j.app U).hom s) := isUnit_of_mul_isUnit_right (show IsUnit (_ * _) from hs.subst (isUnit_jm M hD hU ht))
  obtain ⟨z, hz, hzU, hzU₀⟩ := hM.2 U U₀ U.isOpen U₀.isOpen (Set.inter_comm _ _ ▸ h) (Set.inter_comm _ _ ▸ h₀)
  obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := M.Y.left) (U := U ⊓ U₀) ⟨hzU, hzU₀⟩
  have h1 : V ≤ U := fun _ h => (hle h).1
  have h2 : V ≤ U₀ := fun _ h => (hle h).2
  obtain ⟨a, ha, -⟩ := chain_model M D V _ (fun i => rs _ h2 (t₀ i)) (coord_rs M hU hV h1 ht)
  rw [← rs_jm M D h1, ← rs_jm M D h2, jm, jm, hs, hs₀, map_mul, map_mul, rs_cstK, rs_cstK, rs_j M h1, rs_j M h2, mul_left_comm,
    ← map_mul] at ha
  have hb := j_app_injective M V ((isUnit_cstK hπ _ n).mul_left_cancel ha)
  have hc : IsUnit (rs _ h1 s) := isUnit_of_mul_isUnit_right (hb ▸ hu₀.map (rs _ h2))
  obtain ⟨f, hf⟩ := hjs.exists_right_inv
  obtain ⟨k, b, hk⟩ := exists_pow_mul_eq hπ M hU f
  refine isUnit_of_dvd_pow (prime_cst hπ M hM hU h) (cst_mem_nonZeroDivisors hπ M U) ?_ k ⟨b, ?_⟩
  · intro hd
    have := map_dvd (rs _ h1) hd
    rw [rs_cst] at this
    exact not_isUnit_cst M V ⟨z, hzV, hz⟩ hπ.not_isUnit (isUnit_of_dvd_unit this hc)
  · apply j_app_injective M U
    rw [map_mul, hk, mul_left_comm, hf, _root_.mul_one, map_pow]

section
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}

def th {X : Scheme.{0}} (W : X.Opens) : Γ(X, W) ⟶ Γ(W.toScheme, ⊤) := W.ι.appLE W ⊤ (by simp)

instance {X : Scheme.{0}} (W : X.Opens) : IsIso (th W) := by
  have : th W = W.topIso.inv := by simp [th, Scheme.Opens.topIso, Scheme.Opens.ι_appLE]; rfl
  rw [this]; infer_instance

theorem appLE_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (h' : V ≤ g ⁻¹ᵁ U) : f.appLE U V h = g.appLE U V h' := by
  subst e; rfl

theorem extends_res {M N : Model R A} {U W : M.Y.left.Opens} {g : U.toScheme ⟶ N.Y.left}
    (h : Extends M N (𝟙 A) U g) (hW : W ≤ U) : Extends M N (𝟙 A) W (M.Y.left.homOfLE hW ≫ g) := by
  refine ⟨by rw [Category.assoc, h.1, Scheme.homOfLE_ι_assoc], ?_⟩
  have : M.j ∣_ W ≫ M.Y.left.homOfLE hW = A.left.homOfLE (M.j.preimage_mono hW) ≫ M.j ∣_ U := by
    rw [← cancel_mono U.ι]; simp
  rw [← Category.assoc, this, Category.assoc, h.2, Scheme.homOfLE_ι_assoc]

theorem exists_pull {M N : Model R A} {W : M.Y.left.Opens} {g : W.toScheme ⟶ N.Y.left}
    (h : Extends M N (𝟙 A) W g) (V : N.Y.left.Opens) (hV : ⊤ ≤ g ⁻¹ᵁ V) :
    ∃ (ψ : Γ(N.Y.left, V) →+* Γ(M.Y.left, W)) (hle : M.j ⁻¹ᵁ W ≤ N.j ⁻¹ᵁ V), ψ.comp (cst N V) = cst M W ∧
      (∀ u, (M.j.app W).hom (ψ u) = rs _ hle ((N.j.app V).hom u)) ∧
      (IsAffineOpen W → IsAffineOpen V → ψ.Etale → Etale g) := by
  have h2 : M.j ∣_ W ≫ g = (M.j ⁻¹ᵁ W).ι ≫ N.j := by simpa using h.2
  have hle : M.j ⁻¹ᵁ W ≤ N.j ⁻¹ᵁ V := fun x hx => by
    have : ((M.j ⁻¹ᵁ W).ι ≫ N.j) ⟨x, hx⟩ ∈ V := by
      rw [← h2]; exact hV (x := (M.j ∣_ W) ⟨x, hx⟩) trivial
    exact this
  refine ⟨(g.appLE V ⊤ hV ≫ inv (th W)).hom, hle, ?_, ?_, ?_⟩
  · have : N.Y.hom.appLE ⊤ V le_top ≫ g.appLE V ⊤ hV ≫ inv (th W) = M.Y.hom.appLE ⊤ W le_top := by
      rw [← Category.assoc, IsIso.comp_inv_eq, th, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      exact appLE_congr h.1 _ _ _ _
    ext r
    exact congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) this
  · have a : M.j.app W ≫ th (M.j ⁻¹ᵁ W) = th W ≫ (M.j ∣_ W).appLE ⊤ ⊤ le_top := by
      rw [th, th, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      exact appLE_congr (morphismRestrict_ι _ _).symm _ _ _ _
    have : (g.appLE V ⊤ hV ≫ inv (th W)) ≫ M.j.app W = N.j.appLE V _ hle := by
      rw [← cancel_mono (th (M.j ⁻¹ᵁ W)), Category.assoc, a, Category.assoc, IsIso.inv_hom_id_assoc, th,
        Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      exact appLE_congr h2 _ _ _ _
    intro u
    exact congrArg (fun q => q.hom u) this
  · intro hW hV' he
    have : IsAffine W.toScheme := hW
    have he' : (g.appLE V ⊤ hV).hom.Etale := (RingHom.Etale.respectsIso.cancel_right_isIso _ _).1 he
    have h3 : Etale (g.resLE V ⊤ hV) := by
      have : IsAffine V.toScheme := hV'
      have : IsAffine (⊤ : W.toScheme.Opens).toScheme := isAffineOpen_top _
      rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
      exact (RingHom.Etale.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso g V ⊤ hV)).2 he'
    have h4 : Etale ((⊤ : W.toScheme.Opens).ι ≫ g) := by
      rw [← Scheme.Hom.resLE_comp_ι g hV]; infer_instance
    have h5 : g = W.toScheme.topIso.inv ≫ (⊤ : W.toScheme.Opens).ι ≫ g := by simp
    rw [h5]; infer_instance
end

theorem ord_mono : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) [IsIntegral A.left] (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A), IsFrame D → ∀ (M N : Model R A) (m n : ℤ), M.Irr → N.Irr → HasOrd M D π m → HasOrd N D π n → (∃ y ∈ M.sp, DefAt M N (𝟙 A) y) → m ≤ n ∧ (m = n → GenIso M N (𝟙 A)) := by
  intro R K _ _ _ _ _ _ π hπ A _ I _ _ D hD M N m n hM hN hm hn ⟨y, hy, U, g, hyU, hg⟩
  have hx : g ⟨y, hyU⟩ ∈ N.sp := by
    have : (g ≫ N.Y.hom) ⟨y, hyU⟩ = (U.ι ≫ M.Y.hom) ⟨y, hyU⟩ := by rw [hg.1]
    exact this.trans hy
  obtain ⟨V, t, hV, hxV, -, ht⟩ := GlobalTheory.SS.Ord.exists_etale_coord R K A I hD.1 N (g ⟨y, hyU⟩) ⊤ trivial
  obtain ⟨s, hs, e⟩ := chart hπ N hN hD hn hV ⟨_, hxV, hx⟩ ht
  obtain ⟨W, r, hW, hyW, hle, hr⟩ := GlobalTheory.SS.Ord.exists_etale_coord R K A I hD.1 M y (U.ι ''ᵁ g ⁻¹ᵁ V) ⟨⟨y, hyU⟩, hxV, rfl⟩
  have hWU : W ≤ U := hle.trans (U.ι_image_le _)
  have hg' := extends_res hg hWU
  have htop : ⊤ ≤ (M.Y.left.homOfLE hWU ≫ g) ⁻¹ᵁ V := by
    intro z _
    obtain ⟨w, hw, e⟩ := hle z.2
    have : M.Y.left.homOfLE hWU z = w := Subtype.ext (by rw [Scheme.homOfLE_apply]; exact e.symm)
    show g (M.Y.left.homOfLE hWU z) ∈ V
    rw [this]; exact hw
  obtain ⟨ψ, hj, hc, hψ, het⟩ := exists_pull hg' V htop
  have key : jm M D W (fun i => ψ (t i)) = cstK A _ (algebraMap R K π ^ n) * (M.j.app W).hom (ψ s) := by
    have := congrArg (rs _ hj) e
    rw [jm, rs_jac, map_mul, rs_cstK, ← hψ] at this
    simpa only [jm, hψ] using this
  have hp : algebraMap R K π ≠ 0 := by simpa using hπ.ne_zero
  refine ⟨not_lt.1 fun hlt => ?_, ?_⟩
  · obtain ⟨s', e'⟩ := hm.1 W fun i => ψ (t i)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, m = n + (k + 1 : ℕ) := ⟨(m - n - 1).toNat, by omega⟩
    replace e' := key.symm.trans e'
    rw [hk, zpow_add₀ hp, map_mul, _root_.mul_assoc, zpow_natCast, ← map_pow, ← j_cst, ← map_mul] at e'
    have h1 := j_app_injective M W ((isUnit_cstK hπ _ n).mul_left_cancel e')
    have h2 := hs.map ψ
    rw [h1, pow_succ, map_mul] at h2
    exact not_isUnit_cst M W ⟨y, hyW, hy⟩ hπ.not_isUnit (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h2))
  · rintro rfl
    obtain ⟨s', e'⟩ := hm.1 W r
    obtain ⟨a, ha, hb⟩ := chain_model M D W r (fun i => ψ (t i)) hr
    rw [key, jm, e', mul_left_comm, ← map_mul] at ha
    have h1 := j_app_injective M W ((isUnit_cstK hπ _ m).mul_left_cancel ha)
    have h2 := hb (isUnit_of_mul_isUnit_left (show IsUnit (_ * _) from h1.subst (hs.map ψ)))
    have h3 : (ψ.comp (MvPolynomial.eval₂Hom (cst N V) t)).Etale := by
      rw [MvPolynomial.comp_eval₂Hom, hc]; exact h2
    have h4 : ψ.Etale := by
      algebraize [MvPolynomial.eval₂Hom (cst N V) t, ψ, ψ.comp (MvPolynomial.eval₂Hom (cst N V) t)]
      exact Algebra.Etale.of_restrictScalars (R := MvPolynomial I R) _ _
    exact ⟨y, hy, W, _, hyW, hg', GlobalTheory.SS.Ord.isOpenImmersion_of_extends_id_of_etale R K A M N W _ hg' (het hW hV h4)⟩

end GlobalTheory.SS.OrdMono
end
