import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.QhtUnbdd
import Development.WeilBound.ThetaLifts.CartanFactorisation.IntegrableOnRight

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Orth

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl

open PositivityTheory.ThKEst GlobalTheory.SplitFlip PositivityTheory.KCo
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

variable {n' : ℕ} {X' : Spc F E n'}

theorem inv_loc₂ (hL : LocDist) (e : Fin n ⊕ Fin n' ≃ Fin d) {v : Pl F} {om : Rep σ X W} {om' : Rep σ X' W}
    {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)}
    {ι' : ((Fin n' × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n') (Fin d) (Fv F v) → ℂ)}
    (b : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (b' : Set.BijOn ι' (SB (Fin n' × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n') (Fin d) (Fv F v)) : Set _))
    {ν ν' α α' : (Fv F v)ˣ →* ℂˣ} (n1 : ∀ x, ‖(ν x : ℂ)‖ = 1) (n2 : ∀ x, ‖(α x : ℂ)‖ = 1) (hν : ∀ x, ν x = α x / α' x)
    (hne : ν (unifAt v) ≠ 1) (L : ((Fin n' × Fin d → Fv F v) → ℂ) →ₗ[ℂ] Fn F n d →ₛₗ[starRingEnd ℂ] ℂ)
    (hh : ∀ h₀, ∃ h, Reads v ι (om (1, h)) (omB ν α 1 h₀) ∧ Reads v ι' (om' (1, h)) (omB ν' α' 1 h₀) ∧
      ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om' (1, h)) φ φ₁ → ∀ Ψ ∈ schA F _, L φ₁ (om (1, h) Ψ) = L φ Ψ)
    {u g₀} (hu : Reads v ι (om (u, 1)) (omB ν α g₀ 1)) : ∀ φ' ∈ SB _, ∀ Ψ ∈ schA F _, L φ' (om (u, 1) Ψ) = L φ' Ψ := by
  obtain ⟨j, j1, j2⟩ := exists_inv' b
  obtain ⟨j', j1', j2'⟩ := exists_inv' b'
  intro φ' p1' Ψ hΨ
  refine schA_le (LinearMap.eqLocus (L φ' ∘ₛₗ om (u, 1)) (L φ')) (fun f φ p1 p2 => ?_) hΨ
  obtain ⟨T, t1, t2, t3⟩ := intersection_update_fsHerm_neg_one v f p1 p2
  let N : (Fv F v)ˣ →* ℂˣ := MonoidHom.toHomUnits ⟨⟨fun x => apow x ((d : ℂ) / 2), apow_one _⟩, fun x y => apow_mul x y _⟩
  have hN : ∀ x, ((ν * N⁻¹) x : ℂ) = ν x * (apow x ((d : ℂ) / 2))⁻¹ := fun x => by simp [N]
  have cj : ∀ {z : ℂ}, ‖z‖ = 1 → starRingEnd ℂ z = z⁻¹ := fun h => (Complex.inv_eq_conj h).symm
  have cj' : ∀ (x : (Fv F v)ˣ) (m : ℕ), starRingEnd ℂ (apow x ((m : ℂ) / 2)) = apow x ((m : ℂ) / 2) := fun x m => by
    obtain ⟨r, -, h⟩ := apow_real x m
    rw [h, Complex.conj_ofReal]
  let β : SB (Matrix (Fin n) (Fin d) (Fv F v)) →ₗ[ℂ] SB (Matrix (Fin n') (Fin d) (Fv F v)) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun a b => L (j' b.1) (T (j (star a.1)))) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp) fun _ _ _ => by simp
  let g₁ := Matrix.GeneralLinearGroup.mkOfDetNeZero g₀.1ᵀ (by rw [Matrix.det_transpose]; exact g₀.det_ne_zero)
  have key := TC.locBil hL v e (ν * N⁻¹) (fun t ht h => hne (Units.ext ?_)) β (fun a b h₀ => ?_)
    ⟨_, sb_star (b.1 (p1 v))⟩ ⟨_, b'.1 p1'⟩ g₁
  · have k2 := t3 _ _ (p1 v) _ (acts_of_reads hu j2 (p1 v)).2
    rw [omB_left, map_smul, map_smul, t1, Function.update_eq_self] at k2
    change L _ (T (j (star fun y => star (ι (φ v) (g₀.1ᵀ * y))))) = _ * L _ (T (j (star (star _)))) at key
    rw [star_star, j2 _ (p1 v), j2' _ p1', t1 (φ v), Function.update_eq_self, hN,
      show Matrix.GeneralLinearGroup.det g₁ = gdet g₀ from Units.ext (Matrix.det_transpose _), ← Pi.star_def, star_star] at key
    change L _ (om (u, 1) _) = _
    rw [k2, map_smulₛₗ, key, map_mul, cj (n1 _), cj', smul_eq_mul]
    have := apow_ne_zero (gdet g₀) ((d : ℂ) / 2)
    field_simp
  · obtain ⟨r, hr, e1⟩ := apow_real (unifAt v) d
    rw [hN, e1, mul_inv_eq_iff_eq_mul₀ (by exact_mod_cast hr.ne'), ← Complex.ofReal_mul] at h
    have := n1 (unifAt v)
    rw [h, Complex.norm_real, Real.norm_of_nonneg (mul_pos ht hr).le] at this
    rw [h, this]; rfl
  · obtain ⟨h, r1, r2, r3⟩ := hh h₀
    have a1 := j1 _ (sb_star a.2)
    have b1 := j1' _ b.2
    have k1 := t3 _ _ a1.1 _ (acts_of_reads r1 j2 a1.1).2
    have k3 := r3 _ b1.1 _ (acts_of_reads r2 j2' b1.1).1 (acts_of_reads r2 j2' b1.1).2 _ (t2 _ a1.1)
    rw [k1, a1.2, b1.2, omB_right, omB_right] at k3
    simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, cj (n2 _), cj'] at k3
    have hd : (d : ℂ) / 2 = (n : ℂ) / 2 + (n' : ℂ) / 2 := by
      have := Fintype.card_congr e
      simp only [Fintype.card_sum, Fintype.card_fin] at this
      rw [← this]; push_cast; ring
    change L (j' fun y => b.1 (y * h₀.1)) (T (j fun y => star a.1 (y * h₀.1))) = _ * L (j' b.1) (T (j (star a.1)))
    rw [← k3, hN, hν, hd, apow_add]
    have := apow_ne_zero (gdet h₀) ((n : ℂ) / 2)
    have := apow_ne_zero (gdet h₀) ((n' : ℂ) / 2)
    simp only [Units.val_div_eq_div_val]
    field_simp

theorem exists_ext {A A' : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A'] (S : Submodule ℂ A)
    (S' : Submodule ℂ A') (P : A → A' → ℂ) (h1 : ∀ a ∈ S, ∀ b ∈ S, ∀ x ∈ S', P (a + b) x = P a x + P b x)
    (h2 : ∀ (c : ℂ) a x, P (c • a) x = c * P a x) (h3 : ∀ a ∈ S, ∀ x ∈ S', ∀ y ∈ S', P a (x + y) = P a x + P a y)
    (h4 : ∀ (c : ℂ) a, ∀ x ∈ S', P a (c • x) = star c * P a x) :
    ∃ L : A →ₗ[ℂ] A' →ₛₗ[starRingEnd ℂ] ℂ, ∀ a ∈ S, ∀ x ∈ S', L a x = P a x := by
  obtain ⟨q, hq⟩ := S.subtype.exists_leftInverse_of_injective S.ker_subtype
  obtain ⟨q', hq'⟩ := S'.subtype.exists_leftInverse_of_injective S'.ker_subtype
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun a x => P (q a) (q' x))
    (fun a b x => by simpa using h1 _ (q a).2 _ (q b).2 _ (q' x).2) (fun c a x => by simpa using h2 c (q a) (q' x))
    (fun a x y => by simpa using h3 _ (q a).2 _ (q' x).2 _ (q' y).2) (fun c a x => by simpa using h4 c (q a) _ (q' x).2),
    fun a ha x hx => ?_⟩
  exact congrArg₂ P (congrArg Subtype.val (LinearMap.congr_fun hq ⟨a, ha⟩)) (congrArg Subtype.val (LinearMap.congr_fun hq' ⟨x, hx⟩))

theorem uniW (hE : EpsOf) (hU : PositivityTheory.ThKF.Unimod) (hp : IsPair B M χX χW om r s r' s') :
    Countable (ratU σ W.J) ∧ ∀ μ : Measure (UA σ W.J), μ.IsHaarMeasure → μ.IsMulRightInvariant :=
  let h := hU F E σ hp.base.cm d W.J (-1) (fun i j => by simpa using hp.skew.skew i j)
    (hE F E σ B hp.base d W _ _ (Or.inr hp.skew)).1.2
  ⟨h.1, h.2.2⟩

theorem th_right (hB : ThetaBasic) (hE : EpsOf) (hU : PositivityTheory.ThKF.Unimod) (hp : IsPair B M χX χW om r s r' s')
    {μ : Measure (UA σ W.J)} {D : Set (UA σ W.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ W.J) D μ) {f}
    (hf : IsRapid (Y := W) f) {Ψ} (hΨ : Ψ ∈ schA F _) (g h) : th om μ D (fun x => f (x * h)) (om (1, h) Ψ) g = th om μ D f Ψ g := by
  obtain ⟨h1, h2⟩ := uniW hE hU hp
  have := h2 μ hμ
  have : BorelSpace (UA σ W.J) := ⟨rfl⟩
  have e : ∀ x, theta om (om (1, h) Ψ) g x = theta om Ψ g (x * h) := fun x => by
    simp only [theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [th, pet, e]
  exact PositivityTheory.ThKF.L2.integral_right hD (fun x => f x * star (theta om Ψ g x))
    (fun γ hγ x => by simp only [hf.2.1 γ hγ, theta_rat hB hp hΨ g γ hγ]) h

theorem th_addf (hB : ThetaBasic) (hE : EpsOf) (hV : FinVolU) (hp : IsPair B M χX χW om r s r' s') {μ : Measure (UA σ W.J)}
    {D : Set (UA σ W.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ W.J) D μ) {ι : Type} (S : Finset ι)
    {f : ι → UA σ W.J → ℂ} (hf : ∀ i, IsRapid (Y := W) (f i)) {Ψ} (hΨ : Ψ ∈ schA F _) (g) :
    th om μ D (∑ i ∈ S, f i) Ψ g = ∑ i ∈ S, th om μ D (f i) Ψ g := by
  simp only [th, pet, Finset.sum_apply, Finset.sum_mul]
  exact integral_finset_sum _ fun i _ => th_int hB hE hV hp hμ hD (hf i) hΨ g

theorem pairLoc_of (hB : ThetaBasic) (hE : EpsOf) (hV : FinVolU) (hU : PositivityTheory.ThKF.Unimod) (hL : LocDist) (hS : SplitB) :
    PairLoc := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp n' X' M' χX' χW' om' r₁ s₁ hp' hn hχ v t hne μ D hμ hD f
    ⟨m, T, φ, hT, e⟩ Ψ hΨ u hu g
  rw [e, th_addf hB hE hV hp hμ hD _ (fun i => (hT i).1.1 _ (hT i).2) hΨ, th_addf hB hE hV hp hμ hD _ (fun i => (hT i).1.1 _ (hT i).2) hΨ]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨⟨t1, t2⟩, t3⟩ := hT i
  obtain ⟨L, hLP⟩ := exists_ext (SB _) (schA F (Fin n × Fin d)) (fun a x => th om μ D (T i a) x g)
    (fun a ha b hb x hx => by
      simp only [th, pet, map_add, Pi.add_apply, add_mul]
      exact integral_add (th_int hB hE hV hp hμ hD (t1 a ha) hx g) (th_int hB hE hV hp hμ hD (t1 b hb) hx g))
    (fun c a x => by simp only [th, pet, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul])
    (fun a ha x hx y hy => th_add hB hE hV hp hμ hD (t1 a ha) hx hy g) fun c a x hx => th_smul hp μ D _ c hx g
  obtain ⟨o1, ι, b, l1, r1⟩ := hS F E σ B n d X W M χX χW om r s r' s' hp v t
  obtain ⟨-, ι', b', -, r2⟩ := hS F E σ B n' d X' W M' χX' χW' om' r₁ s₁ r' s' hp' v t
  obtain ⟨g₀, hg₀⟩ := l1 u hu
  have pr := (IsUWeilPair.isUSplitting hp.weil).pres
  rw [← th_left, ← hLP _ t3 _ (pr _ _ hΨ), ← hLP _ t3 _ hΨ]
  refine inv_loc₂ hL (finSumFinEquiv.trans (finCongr hn)) b b' (ν' := chrW χW' t) (α' := chrW χX' t) (om' := om')
    (fun x => Circle.norm_coe _) (fun x => Circle.norm_coe _) (fun x => ?_) hne L (fun h₀ => ?_) hg₀ _ t3 Ψ hΨ
  · simp only [hχ, chrW, locChar, MonoidHom.comp_apply, MonoidHom.div_apply, map_div]
  · obtain ⟨h, hh, e₀⟩ := o1 h₀
    refine ⟨h, r1 h hh h₀ e₀, r2 h hh h₀ e₀, fun a ha a₁ ha₁ hA x hx => ?_⟩
    rw [hLP _ ha₁ _ (pr _ _ hx), hLP _ ha _ hx, t2 h hh a ha a₁ ha₁ hA, th_right hB hE hU hp hμ hD (t1 a ha) hx]

end PositivityTheory.ThKEnd.Orth

end
