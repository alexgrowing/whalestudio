import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MixInvariantPlaneDecomposition
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MixSignTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ResidualCharactersPsiNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.IrrAb
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ResFacts

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Sd.S2

private theorem conjHom {Γ₀ Γ : Type} [Group Γ₀] [Group Γ] (j : Γ₀ →* Γ) (hj : Function.Injective j) (hi : j.range.index = 2)
    (t : Γ) : ∃ c : Γ₀ →* Γ₀, ∀ h, j (c h) = t⁻¹ * j h * t := by
  have hn : j.range.Normal := Subgroup.normal_of_index_eq_two hi
  have : ∀ h, ∃ h', j h' = t⁻¹ * j h * t := fun h => hn.conj_mem' _ ⟨h, rfl⟩ t
  choose c hc using this
  refine ⟨MonoidHom.mk' c fun a b => hj ?_, hc⟩
  rw [map_mul, hc, hc, hc, map_mul]; group

private theorem cp_conj {K : Type} [Field K] (g r : GL (Fin 2) K) :
    ((g * r * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly = (r : Matrix (Fin 2) (Fin 2) K).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj g _

private theorem cp_ord {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
    {r : G F Ω →* GL (Fin 2) (Qbar l)} {a b : ℤ} {ψ : Fin 2 → G F Ω →* (Qbar l)ˣ} {A : ValuationSubring Ω}
    (h : OrdAt r ![a, b] ψ A) {s : G F Ω} (hs : s ∈ Ine (F := F) A) :
    (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly =
      (X - C ((cycBar F Ω l s ^ a : (Qbar l)ˣ) : Qbar l)) * (X - C ((cycBar F Ω l s ^ b : (Qbar l)ˣ) : Qbar l)) := by
  obtain ⟨κ, ⟨g, hg⟩, hκ, -⟩ := h
  let s' : ↥(Dec (F := F) A) := ⟨s, Ine_le_Dec A hs⟩
  have h0 := (hg s').2 0
  have h1 := (hg s').2 1
  rw [hκ 0 s' hs] at h0
  rw [hκ 1 s' hs] at h1
  rw [← cp_conj g, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => (hg s').1 i j hij), Fin.prod_univ_two]
  exact congrArg₂ (fun x y => (X - C x) * (X - C y)) h0 h1

private theorem cp_ne {K : Type} [Field K] (e : Kˣ) (he : ¬ IsOfFinOrder e) (k t : ℕ) (ht : 2 ≤ t) :
    (X - C ((e ^ ((k : ℤ) + t) : Kˣ) : K)) * (X - C ((e ^ (-(t : ℤ)) : Kˣ) : K)) ≠
      (X - C ((e ^ (k : ℤ) : Kˣ) : K)) * (X - C ((e ^ (0 : ℤ) : Kˣ) : K)) := by
  intro h
  have h1 := congrArg (Polynomial.eval 1) h
  simp only [eval_mul, eval_sub, eval_X, eval_C, zpow_zero, Units.val_one, sub_self, mul_zero, mul_eq_zero] at h1
  have hinj := injective_zpow_iff_not_isOfFinOrder.2 he
  rcases h1 with h1 | h1
  · have : e ^ ((k : ℤ) + t) = e ^ (0 : ℤ) := Units.ext (by rw [zpow_zero, Units.val_one]; exact (sub_eq_zero.1 h1).symm)
    have := hinj this
    omega
  · have : e ^ (-(t : ℤ)) = e ^ (0 : ℤ) := Units.ext (by rw [zpow_zero, Units.val_one]; exact (sub_eq_zero.1 h1).symm)
    have := hinj this
    omega

private theorem range_res {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (E : IntermediateField ℚ Ω) :
    (resQ E).range = E.fixingSubgroup := by
  refine (range_galEmb ℚ E Ω).trans ?_
  ext g
  rw [mem_galOf, IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x x.2⟩

private theorem ine_move {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (g x : G ℚ Ω)
    (hx : x ∈ Ine (F := ℚ) A) : g⁻¹ * x * g ∈ Ine (F := ℚ) (A.comap g.toRingEquiv.toRingHom) := by
  have h : UpperTheory.V.IsLift (RingEquiv.refl ℚ) g.toRingEquiv := fun x => g.commutes x
  exact UpperTheory.V.conjGal_mem_Ine h (fun _ => Iff.rfl) hx

theorem UpperTheory.induced_irreducible :
    UpperTheory.V.Sd.S2.IndIrr := by
  intro Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r α β R δ hd
  haveI : IsGalois ℚ Ω := {}
  haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) k₀⟩
  set τ : G ℚ Ω := resQ T.F T.g0 with hτ
  let V : Subgroup (G ℚ Ω) := T.F.fixingSubgroup ⊓ T.K.fixingSubgroup
  let U : Subgroup (G ℚ Ω) := V ⊓ (cycZ ℚ Ω l).ker
  have hV : IsOpen (V : Set (G ℚ Ω)) := T.F.fixingSubgroup_isOpen.inter T.K.fixingSubgroup_isOpen
  have hU : ∀ g ∈ T.G', resQ T.F g ∈ U := fun g hg => ⟨⟨range_res T.F ▸ ⟨g, rfl⟩, hg.1⟩, hg.2⟩
  have hU' : ∀ g ∈ U, ∃ g' ∈ T.G', resQ T.F g' = g := by
    intro g hg
    obtain ⟨g', rfl⟩ : g ∈ (resQ T.F).range := range_res T.F ▸ hg.1.1
    exact ⟨g', ⟨hg.1.2, hg.2⟩, rfl⟩
  have hcont : Continuous (resQ k₀) := (resFacts ℚ k₀ Ω l 1 1).1
  have hirr : IsIrr (r.comp (U.comap (resQ k₀)).subtype) := by
    refine irrAb l _ 2 r hd.dat.cont hd.dat.irr (V.comap (resQ k₀)) _ (hV.preimage hcont) (Subgroup.comap_mono inf_le_left) ?_
    intro a ha b hb
    refine ⟨(V.comap (resQ k₀)).mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb), ?_⟩
    show cycZ ℚ Ω l (resQ k₀ (a * b * a⁻¹ * b⁻¹)) = 1
    simp only [map_mul, map_inv]
    rw [mul_inv_cancel_comm, mul_inv_cancel]
  have key : IsIrr (R.comp U.subtype) := by
    refine UpperTheory.mix_invariant_plane_decomposition _ _ _ (resQ k₀) τ α β r R hd.mix U ?_ hirr ?_
    · obtain ⟨g, hg, hne⟩ := UpperTheory.residual_characters_psi_ne Ω l c D T hd.hyp.good hd.hyp.ok hd.hyp.two
      intro hle
      exact hne ((hd.hyp.ps g).2 (range_res k₀ ▸ hle (hU g hg)))
    · rintro ⟨M, hM⟩
      obtain ⟨cj, hcj⟩ := conjHom (resQ k₀) hd.mix.inj hd.mix.index τ
      have hchar : ∀ (χ : G ℚ Ω →* (Qbar l)ˣ) (h : G k₀ Ω), χ (resQ k₀ (cj h)) = χ (resQ k₀ h) := by
        intro χ h
        rw [hcj, map_mul, map_mul, map_inv, inv_mul_cancel_comm]
      have hcyc : ∀ h, cycBar k₀ Ω l (cj h) = cycBar k₀ Ω l h := hchar (cycBar ℚ Ω l)
      let H : Subgroup (G ℚ Ω) := V ⊓ k₀.fixingSubgroup
      have hH : IsOpen (H : Set (G ℚ Ω)) := hV.inter k₀.fixingSubgroup_isOpen
      haveI : Finite (G ℚ Ω ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
      haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      obtain ⟨n, hn, -, hnH⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (H := H) Subgroup.FiniteIndex.index_ne_zero
        (D.s0 : G ℚ Ω)
      obtain ⟨s, hs⟩ : (D.s0 : G ℚ Ω) ^ n ∈ (resQ k₀).range := range_res k₀ ▸ hnH.2
      have hsV : resQ k₀ s ∈ V := hs ▸ hnH.1
      have hsI : resQ k₀ (s * s) ∈ Ine (F := ℚ) (D.pl l) := by
        rw [map_mul, hs]
        exact mul_mem (pow_mem hd.hyp.good.decompSigma_mem.1.1 n) (pow_mem hd.hyp.good.decompSigma_mem.1.1 n)
      have hdet : ∀ h, Matrix.GeneralLinearGroup.det (r h) = cycBar k₀ Ω l h ^ k * up D.ξ (resQ k₀ h) :=
        fun h => DFunLike.congr_fun hd.dat.det h
      have hsq := UpperTheory.mix_sign_twist _ _ r (r.comp cj) (U.comap (resQ k₀)) M hirr (fun h hh => hM h (cj h) hh (hcj h)) s
        (fun h hh => ⟨(V.comap (resQ k₀)).mul_mem ((V.comap (resQ k₀)).mul_mem hsV hh.1) ((V.comap (resQ k₀)).inv_mem hsV), by
          have h1 : cycZ ℚ Ω l (resQ k₀ h) = 1 := hh.2
          show cycZ ℚ Ω l (resQ k₀ (s * h * s⁻¹)) = 1
          simp only [map_mul, map_inv, h1, mul_one, mul_inv_cancel]⟩)
        (by rw [MonoidHom.comp_apply, hdet, hdet, hcyc, hchar])
      have hcp : (r (cj (s * s)) : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly =
          (r (s * s) : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly := by
        rw [← cp_conj M (r (s * s)), ← hsq]; rfl
      have hI : s * s ∈ Ine (F := k₀) (D.pl l) := mem_Ine.2 (mem_Ine.1 hsI)
      have hI' : cj (s * s) ∈ Ine (F := k₀) ((D.pl l).comap τ.toRingEquiv.toRingHom) := by
        have := ine_move (D.pl l) τ _ hsI
        rw [← hcj] at this
        exact mem_Ine.2 (mem_Ine.1 this)
      have he : ¬ IsOfFinOrder (cycBar k₀ Ω l (s * s)) := by
        have hinj : Function.Injective
            (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) :=
          Units.map_injective ((algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective)
        intro hf
        have h1 : IsOfFinOrder (cycZ ℚ Ω l (resQ k₀ (s * s))) := (hinj.isOfFinOrder_iff).1 hf
        rw [map_mul, hs, ← pow_add, map_pow] at h1
        exact hd.hyp.good.decompSigma_ord (h1.of_pow (by omega))
      rcases hd.dat.above (D.pl l) ((D.pl l).comap τ.toRingEquiv.toRingHom) (hd.hyp.good.pl_over l Fact.out) τ
        hd.chars.out (fun _ => Iff.rfl) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [cp_ord h1 hI, cp_ord h2 hI', hcyc] at hcp
        exact cp_ne _ he k t hd.dat.ht hcp.symm
      · rw [cp_ord h1 hI, cp_ord h2 hI', hcyc] at hcp
        exact cp_ne _ he k t hd.dat.ht hcp
  refine ⟨key.1, fun _ _ _ => trivial, fun W hW hi => key.2.2 W hW ?_⟩
  rintro ⟨g, hg⟩ v hv
  obtain ⟨g', hg', rfl⟩ := hU' g hg
  exact hi ⟨g', hg'⟩ v hv
