import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProduct
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqEmbed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqMult
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwThetaEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools GlobalTheory.PRep

private theorem jqLine_eig {T W : Type} [CommGroup T] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    [Nontrivial W] (θ : T →* (Module.End ℂ W)ˣ) :
    ∃ χ : T →* ℂˣ, (⨅ t, Module.End.maxGenEigenspace (θ t : Module.End ℂ W) (χ t : ℂ)) ≠ ⊥ := by
  obtain ⟨S, ⟨hS0, hS⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ W)).has_min
    {S | S ≠ ⊥ ∧ ∀ t, ∀ v ∈ S, (θ t : Module.End ℂ W) v ∈ S} ⟨⊤, top_ne_bot, fun _ _ _ => trivial⟩
  have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS0
  have key : ∀ t, ∃ c : ℂ, ∀ v ∈ S, (θ t : Module.End ℂ W) v = c • v := fun t => by
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((θ t : Module.End ℂ W).restrict (hS t))
    obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
    have hw1 : (θ t : Module.End ℂ W) w = c • (w : W) := congrArg Subtype.val hw.apply_eq_smul
    refine ⟨c, fun v hv => ?_⟩
    have h1 : S ⊓ Module.End.eigenspace (θ t : Module.End ℂ W) c = S := by
      by_contra hne
      refine hmin _ ⟨?_, ?_⟩ (lt_of_le_of_ne inf_le_left hne)
      · exact (Submodule.ne_bot_iff _).2 ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩,
          fun h => hw.2 (Subtype.ext h)⟩
      · rintro s x ⟨hx, hx'⟩
        refine ⟨hS s x hx, Module.End.mem_eigenspace_iff.2 ?_⟩
        rw [← Module.End.mul_apply, ← Units.val_mul, ← map_mul, mul_comm, map_mul, Units.val_mul,
          Module.End.mul_apply, Module.End.mem_eigenspace_iff.1 hx', map_smul]
    rw [← h1] at hv
    exact Module.End.mem_eigenspace_iff.1 hv.2
  choose c hc using key
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hS0
  let c' : T →* ℂ :=
    { toFun := c
      map_one' := by
        have := hc 1 v hv
        rw [map_one, Units.val_one, Module.End.one_apply] at this
        exact smul_left_injective ℂ hv0 (this.symm.trans (one_smul _ _).symm)
      map_mul' := fun s t => by
        have := hc (s * t) v hv
        rw [map_mul, Units.val_mul, Module.End.mul_apply, hc t v hv, map_smul, hc s v hv, smul_smul,
          mul_comm] at this
        exact smul_left_injective ℂ hv0 this.symm }
  refine ⟨c'.toHomUnits, (Submodule.ne_bot_iff _).2 ⟨v, (Submodule.mem_iInf _).2 fun t => ?_, hv0⟩⟩
  refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, ?_⟩
  rw [pow_one, LinearMap.sub_apply, hc t v hv]
  simp [c']

private theorem jqLine_map {W J : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup J] [Module ℂ J]
    (f : W →ₗ[ℂ] J) (a : Module.End ℂ W) (b : Module.End ℂ J) (d : ℂˣ) (c : ℂ)
    (h : ∀ v, f (a v) = ((d⁻¹ : ℂˣ) : ℂ) • b (f v)) {v : W} (hv : v ∈ a.maxGenEigenspace c) :
    f v ∈ b.maxGenEigenspace (c * d) := by
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
  refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨m, ?_⟩
  have h1 : ∀ x, (b - (c * d) • (1 : Module.End ℂ J)) (f x) = (d : ℂ) • f ((a - c • (1 : Module.End ℂ W)) x) := by
    intro x
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, h, smul_sub,
      smul_smul, Units.mul_inv, one_smul, mul_comm c]
  have h2 : ∀ (m : ℕ) x, ((b - (c * d) • (1 : Module.End ℂ J)) ^ m) (f x) =
      (d : ℂ) ^ m • f (((a - c • (1 : Module.End ℂ W)) ^ m) x) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ', pow_succ' (a - _), Module.End.mul_apply, Module.End.mul_apply, ih, map_smul, h1, smul_smul,
        pow_succ]
  rw [h2, hm, map_zero, smul_zero]

private theorem jqLine_inj {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} {ψ ψ' : Fin n → kˣ →* ℂˣ} (h : torusChar ψ = torusChar ψ') : ψ = ψ' := by
  funext i
  refine MonoidHom.ext fun x => ?_
  have := DFunLike.congr_fun h (Pi.mulSingle i x)
  rw [torusChar_apply, torusChar_apply,
    Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj]) (by simp),
    Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj]) (by simp)] at this
  simpa using this

theorem UpperTheory.V.AlgebraTools.jqLine :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible → FiniteDimensional ℂ (fixd π (iwC k n C)) ∧ Module.finrank ℂ (fixd π (iwC k n C)) ≤ n.factorial ∧ ∀ θ : (Fin n → kˣ) →* (Module.End ℂ (fixd π (iwC k n C)))ˣ, (∀ t, Dom t → (θ t : Module.End ℂ (fixd π (iwC k n C))) = hk π (iwC k n C) (diagT k (Fin n) t)) → ∀ (χ : (Fin n → kˣ) →* ℂˣ) (ψ : Fin n → kˣ →* ℂˣ), Function.Injective ψ → torusChar ψ = χ * ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) → Module.finrank ℂ (⨅ t, Module.End.maxGenEigenspace (θ t : Module.End ℂ (fixd π (iwC k n C))) (χ t : ℂ) : Submodule ℂ (fixd π (iwC k n C))) ≤ 1 := by
  intro hG hBZ k _ _ _ _ n C V _ _ π hs hirr
  have ho : IsOpen (iwC k n C : Set (GL (Fin n) k)) :=
    Subgroup.isOpen_mono (H₁ := KOne k (Fin n)) (le_sup_left.trans le_sup_left) GlobalTheory.StepData.isOpen_KOne
  have hle : iwC k n C ≤ iwahori k (Fin n) := fun g hg => (((memIwC k n C).1 g).1 hg).1
  have hc : IsCompact (iwC k n C : Set (GL (Fin n) k)) :=
    (IwahoriOnto.isCompact_iwahori k (Fin n)).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) hle
  have hfix : fixd π (iwC k n C) = fixed π (iwC k n C) := by
    ext v
    exact ⟨fun h u => by simpa using h u u.2, fun h u hu => by simpa using h ⟨u, hu⟩⟩
  have hfd : FiniteDimensional ℂ (fixd π (iwC k n C)) := by
    rw [hfix]
    exact ((hBZ k).1 _ V π hs hirr).2 _ ho hc
  let f : fixd π (iwC k n C) →ₗ[ℂ] Jacquet π (unipB k (Fin n)) :=
    (Submodule.mkQ _).comp (fixd π (iwC k n C)).subtype
  have hf : Function.Injective f :=
    (injective_iff_map_eq_zero f).2 fun v hv => jqInj k n C V π hs v hv
  refine ⟨hfd, ?_, fun θ hθ χ ψ hψ hχ => ?_⟩
  · rcases subsingleton_or_nontrivial (fixd π (iwC k n C)) with h | h
    · rw [Module.finrank_zero_of_subsingleton]
      exact Nat.zero_le _
    have hq : IsUnit (resCard k : ℂ) := (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[k])).ne').isUnit
    obtain ⟨θ, hθ, -⟩ := thetaEx k n C ℂ V π hq
    obtain ⟨χ, hχ⟩ := jqLine_eig θ
    obtain ⟨ψ, h1, -, -, h2⟩ := jqEmbed hBZ k n C V π hs hirr θ hθ χ hχ
    obtain ⟨h3, h4, -⟩ := jqMult hG hBZ k n V π ψ hs h1 h2
    exact (LinearMap.finrank_le_finrank_of_injective hf).trans h4
  · by_cases h0 : (⨅ t, Module.End.maxGenEigenspace (θ t : Module.End ℂ (fixd π (iwC k n C))) (χ t : ℂ)) = ⊥
    · rw [h0, finrank_bot]
      exact Nat.zero_le _
    obtain ⟨ψ', h1, -, e, h2⟩ := jqEmbed hBZ k n C V π hs hirr θ hθ χ h0
    obtain rfl : ψ = ψ' := jqLine_inj (hχ.trans e.symm)
    obtain ⟨h3, -, h4⟩ := jqMult hG hBZ k n V π ψ hs h1 h2
    have h5 : Nat.card {w : Equiv.Perm (Fin n) // torusChar ψ = torusChar (ψ ∘ w)} ≤ 1 := by
      refine Finite.card_le_one_iff_subsingleton.2 ⟨fun a b => Subtype.ext (Equiv.ext fun i => hψ ?_)⟩
      exact (congrFun (jqLine_inj a.2) i).symm.trans (congrFun (jqLine_inj b.2) i)
    refine le_trans ?_ ((h4 (torusChar ψ)).trans h5)
    rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hf _)]
    refine Submodule.finrank_mono ?_
    rintro _ ⟨v, hv, rfl⟩
    refine (Submodule.mem_iInf _).2 fun t => ?_
    rw [hχ, MonoidHom.mul_apply, Units.val_mul]
    exact jqLine_map f _ _ _ _ (fun v => jqTheta k n C V π θ hθ t v) ((Submodule.mem_iInf _).1 hv t)
