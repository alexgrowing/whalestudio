import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.ConjHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.TrRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Polar
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.ZOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.DerPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.LcMat
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.BarOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.StarFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem lift_smul {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ}
    {E : Type} [Ring E] [Algebra R E] {x : R →ₐ[O] O} {δ : R →ₗ[O] X} {ρ : E →+* Matrix (Fin n) (Fin n) O}
    {τ : E → R} {c : O} {d : E →+ Matrix (Fin n) (Fin n) X} (h : IsLift x δ ρ τ c d) (a : O) :
    IsLift x δ ρ τ (a * c) (a • d) where
  mul u v := by simp only [AddMonoidHom.smul_apply, h.mul, smul_add, Matrix.smul_mul, Matrix.mul_smul]
  smul r u := by
    simp only [AddMonoidHom.smul_apply, h.smul, smul_add]
    rw [smul_comm a (x r), mul_smul, smul_assoc a]
  tr u := by simp only [AddMonoidHom.smul_apply, Matrix.trace_smul, h.tr, mul_smul]

private theorem lc_mat {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
  have : ∀ᶠ g' in nhds g, ∀ i j, f g' i j = f g i j :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (h i j).eventually_eq g
  exact this.mono fun g' e => Matrix.ext e

private theorem der_const {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X] [Module O X] {x : R →ₐ[O] O}
    {δ : R →ₗ[O] X} (h : IsDer x δ) (a : O) : δ (algebraMap O R a) = 0 := by
  have h1 := h 1 1
  rw [mul_one, map_one x, one_smul] at h1
  have h2 : δ 1 = 0 := by simpa using h1
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h2, smul_zero]

theorem UpperTheory.V.Th.coc :
    Coc := by
  intro l hl L G0 n O _ _ _ hO _ y h2 hn
  classical
  obtain ⟨c₀, hc₀, hsp⟩ := y.span
  choose c₁ hc₁ hloc using fun v => locAt y v
  have h2O : (2 : O) ≠ 0 := by
    intro e
    haveI := hO.char
    have h3 : ((2 : ℕ) : ResidueField O) = 0 := by
      rw [← map_natCast (residue O), Nat.cast_ofNat, e, map_zero]
    exact h2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 ((CharP.cast_eq_zero_iff _ l 2).1 h3))
  refine ⟨(∏ v, c₁ v) * (c₀ * (2 * (c₀ ^ (2 * n) * c₀ ^ (2 * n)))),
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun v _ => hc₁ v) (mul_ne_zero hc₀ (mul_ne_zero h2O
      (mul_ne_zero (pow_ne_zero _ hc₀) (pow_ne_zero _ hc₀)))), ?_⟩
  intro G h rN R _ _ _ p x hI hp m δ hδ
  have hsurj : Function.Surjective h.p₀ := fun g => by
    obtain ⟨g', e⟩ := h.surj g
    exact ⟨⟨g', by rw [MonoidHom.mem_ker, ← h.η, e]; exact g.2⟩, Subtype.ext e⟩
  have hcont : Continuous h.p₀ := (h.cont.comp continuous_subtype_val).subtype_mk _
  have hsp' : ∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range (mat (y.ρ.comp h.p₀))) := fun Z => by
    have e : Set.range (mat (y.ρ.comp h.p₀)) = Set.range (mat y.ρ) := hsurj.range_comp (mat y.ρ)
    rw [e]
    exact hsp Z
  have hform : G.frame.IsForm O n (y.ρ.comp h.p₀) y.P := fun g => by
    have e1 : h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g) := Subtype.ext (by
      change h.p (G.c * g * G.c⁻¹) = G0.c * h.p g * G0.c⁻¹
      rw [map_mul, map_mul, map_inv, h.c])
    have e2 : G.frame.eps O O g = G0.frame.eps O O (h.p₀ g) := by
      change Units.map _ (G.ε g) = Units.map _ (G0.ε (h.p g))
      rw [h.ε]
    have := y.form (h.p₀ g)
    rw [← e1, ← e2] at this
    exact this
  obtain ⟨htr, -, t, ht⟩ := trRep p.D x _ hn hp.1
  have ht' : (t : _ → R) = p.D.tr := funext ht
  obtain ⟨d1, hd1⟩ := liftG p.D rN.chib x δ _ c₀ hn rN.chib_inj p.red hp.1 hc₀ hsp' hδ
  obtain ⟨d2, hd2, hpol⟩ := polar G.frame x δ _ y.P t _ d1 y.sgn hform (fun g => by rw [ht, ht]; exact p.P 1 g) (ht' ▸ hd1)
  rw [ht'] at hd2
  have hk := kill x δ _ _ _ c₀ d2 hc₀ hsp' htr hd2
  have hd3 := lift_smul hd2 c₀
  have hd4 := lift_smul hd3 (∏ v, c₁ v)
  obtain ⟨h1, hcoc, hP, hT⟩ := zOf G.frame x δ _ y.P _ _ _
    (fun g => ((∏ v, c₁ v) • c₀ • d2) (MonoidAlgebra.single g 1) * bar (Om O m) (mat (y.ρ.comp h.p₀) g⁻¹)) hδ hform hd4
    (fun a => by simp only [AddMonoidHom.smul_apply, Matrix.mul_smul, Matrix.transpose_smul, Matrix.smul_mul, hpol]) fun _ => rfl
  have hρlc : IsLocallyConstant fun g => bar (Om O m) (mat (y.ρ.comp h.p₀) g) :=
    (lc_mat _ fun i j => (lcDer (R := R) m).1 _ (y.cont i j)).comp_continuous hcont
  refine ⟨_, ⟨?_, hcoc, hP, fun u g hg => ?_, fun v => ?_⟩, hT⟩
  · have hl2 := lc x δ _ _ _ c₀ d2 hsp' hd2 hρlc ((lcDer m).2 x δ hδ _ (p.cont 1))
    exact (hl2.comp fun Z => (∏ v, c₁ v) • Z).mul (hρlc.comp_continuous continuous_inv)
  · have h4 := (hk _ (p.I u g (hI u ▸ hg))).2
    have h5 : d2 1 = 0 := by
      have := hd2.mul 1 1
      simpa using this
    rw [map_sub, h5, sub_zero] at h4
    simp only [AddMonoidHom.smul_apply, h4, smul_zero, Matrix.zero_mul]
  · obtain ⟨Y, hY⟩ := hloc v G h R x m δ _ _ _ (p.ψ v) hd3
      (fun i g => congrArg Units.val (DFunLike.congr_fun (hp.2 v i) g))
      (fun g => hk _ (p.Ord v g)) fun i g hg => by
        rw [(p.psi v i).mu ⟨g, hg⟩]
        exact der_const hδ _
    refine ⟨(∏ v' ∈ Finset.univ.erase v, c₁ v') • Y, fun g => ?_⟩
    have e : ((∏ v, c₁ v) • c₀ • d2) (MonoidAlgebra.single (G.frame.φ v g) 1) *
          bar (Om O m) (mat (y.ρ.comp h.p₀) (G.frame.φ v g)⁻¹) -
        dY G.frame (y.ρm h m) ((∏ v' ∈ Finset.univ.erase v, c₁ v') • Y) (G.frame.φ v g) =
        (∏ v' ∈ Finset.univ.erase v, c₁ v') • (c₁ v • ((c₀ • d2) (MonoidAlgebra.single (G.frame.φ v g) 1) *
          y.ρm h m (G.frame.φ v g)⁻¹) - dY G.frame (y.ρm h m) Y (G.frame.φ v g)) := by
      rw [smul_sub, smul_smul (∏ v' ∈ Finset.univ.erase v, c₁ v'), Finset.prod_erase_mul _ _ (Finset.mem_univ v),
        AddMonoidHom.smul_apply, Matrix.smul_mul]
      simp only [dY, smul_sub, Matrix.mul_smul, Matrix.smul_mul]
      rfl
    rw [e]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply]
    refine ⟨fun i j hij => ?_, fun hg i => ?_⟩
    · have := (hY g).1 i j hij
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply] at this
      rw [this, smul_zero]
    · have := (hY g).2 hg i
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply] at this
      rw [this, smul_zero]
