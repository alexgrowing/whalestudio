import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.IsoFix
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ThetaLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.SphLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.NilKill
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkBern
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwBernHk
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkEv
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwThetaTie
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwSphEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwThetaEx
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem sphScalar_ev {G M M' : Type} [Group G] [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    (ρ : Representation ℂ G M) (ρ' : Representation ℂ G M') (I : Subgroup G) (hI : HeckePair I)
    (ev : HkAlg ℂ I →ₐ[ℂ] Module.End ℂ (fixd ρ I)) (hev : ∀ x, ev (hT ℂ I x) = hk ρ I x)
    (ev' : HkAlg ℂ I →ₐ[ℂ] Module.End ℂ (fixd ρ' I)) (hev' : ∀ x, ev' (hT ℂ I x) = hk ρ' I x)
    (f : M →ₗ[ℂ] M') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (T : HkAlg ℂ I) (v : fixd ρ I) (v' : fixd ρ' I)
    (hv : (v' : M') = f v) : (ev' T v' : M') = f (ev T v) := by
  let g : fixd ρ I →ₗ[ℂ] fixd ρ' I := f.restrict fun x hx u hu => by rw [← hf, hx u hu]
  obtain rfl : v' = g v := Subtype.ext hv
  suffices h : ev' T (g v) = g (ev T v) from congrArg Subtype.val h
  clear hv
  obtain ⟨T, hT'⟩ := T
  induction hT' using Algebra.adjoin_induction generalizing v with
  | mem T h =>
    obtain ⟨x, rfl⟩ := h
    refine (LinearMap.congr_fun (hev' x) _).trans (Eq.trans ?_ (congrArg g (LinearMap.congr_fun (hev x) v)).symm)
    apply Subtype.ext
    refine ((hkApply ℂ _ M' ρ' _ _ _ (hI x)).1 (g v)).trans ?_
    refine ((dcSum ℂ G M ρ I I x (hI x)).2.2.2 ℂ M' ρ' f.toAddMonoidHom hf v).symm.trans ?_
    exact congrArg f ((hkApply ℂ _ M ρ _ _ _ (hI x)).1 v).symm
  | algebraMap c =>
    change ev' (algebraMap ℂ _ c) _ = g (ev (algebraMap ℂ _ c) _)
    rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  | add T T' h1 h2 h h' =>
    change ev' (⟨T, h1⟩ + ⟨T', h2⟩) _ = g (ev (⟨T, h1⟩ + ⟨T', h2⟩) _)
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, h, h']
  | mul T T' h1 h2 h h' =>
    change ev' (⟨T, h1⟩ * ⟨T', h2⟩) _ = g (ev (⟨T, h1⟩ * ⟨T', h2⟩) _)
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h', h]

private theorem sphScalar_int {W W' κ : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (act : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ W) (act' : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ W') (g : W →ₗ[ℂ] W')
    (h : ∀ a v, act' (MvPolynomial.X a) (g v) = g (act (MvPolynomial.X a) v)) (F : MvPolynomial κ ℂ) (v : W) :
    act' F (g v) = g (act F v) := by
  induction F using MvPolynomial.induction_on generalizing v with
  | C c =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes]
    simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p a hp => simp [h, hp]

private theorem sphScalar_tr {W W' κ : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (act : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ W) (act' : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ W') (g : W →ₗ[ℂ] W')
    (hg : Function.Injective g) (a : κ → ℂ) (u : κ → Module.End ℂ W) (u' : κ → Module.End ℂ W')
    (hu : ∀ i, act (MvPolynomial.X i) = a i • u i) (hu' : ∀ i, act' (MvPolynomial.X i) = a i • u' i)
    (h : ∀ i v, u' i (g v) = g (u i v)) (F : MvPolynomial κ ℂ) (c : ℂ) (v : W) (hv : act' F (g v) = c • g v) :
    act F v = c • v := by
  apply hg
  rw [← sphScalar_int act act' g (fun i v => ?_), map_smul, hv]
  rw [hu, hu', LinearMap.smul_apply, LinearMap.smul_apply, map_smul, h]

private theorem sphScalar_nil {W : Type} [AddCommGroup W] [Module ℂ W] (φ : Module.End ℂ W) (c c' : ℂ) (N : ℕ) (m : W)
    (h : φ m = c' • m) (hN : (φ - algebraMap ℂ _ c) ^ N = 0) : φ m = c • m := by
  have h1 : ∀ k : ℕ, ((φ - algebraMap ℂ _ c) ^ k) m = (c' - c) ^ k • m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, h, Module.algebraMap_end_apply,
        ← sub_smul, smul_smul, pow_succ]
  have h2 := h1 N
  rw [hN, LinearMap.zero_apply] at h2
  rcases smul_eq_zero.1 h2.symm with h3 | h3
  · rw [h, sub_eq_zero.1 (pow_eq_zero_iff'.1 h3).1]
  · rw [h3, map_zero, smul_zero]

private theorem sphScalar_gen {G V Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]
    {n : ℕ} {q : ℂ} (ρ : Representation ℂ G V) (π : Representation ℂ G Y) (I K : Subgroup G) (hle : I ≤ K)
    (hI : HeckePair I) (b : Hk.Bern n q (HkAlg ℂ I)) (p : Equiv.Perm (Fin n) → G) (hb : ∀ w, b.T w = hT ℂ I (p w))
    (ev : HkAlg ℂ I →ₐ[ℂ] Module.End ℂ (fixd π I)) (hev : ∀ x, ev (hT ℂ I x) = hk π I x)
    (hs : ∀ v : fixd ρ I, (v : V) ∈ fixd ρ K ↔
      ∀ i j : Fin n, (j : ℕ) = i + 1 → hk ρ I (p (Equiv.swap i j)) v = q • v)
    (hl : ∀ v ∈ fixd ρ K, ∀ v' ∈ fixd ρ K, v ≠ 0 → ∃ c : ℂ, v' = c • v)
    (hiso : ∀ y ∈ fixd π K, y ∈ ⨆ f : {f : V →ₗ[ℂ] Y // ∀ g v, f (ρ g v) = π g (f v)}, (fixd ρ K).map f.1)
    (z : MvPolynomial (Fin n) ℂ) (hz : z.IsSymmetric) (u : Fin n → Module.End ℂ (fixd π I))
    (hu : ∀ i, ev (b.th (MvPolynomial.X i)) = u i) :
    ∃ act : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Module.End ℂ (fixd π I), (∀ i, act (MvPolynomial.X i) = u i) ∧
      ∃ c : ℂ, ∀ v : fixd π I, (v : Y) ∈ fixd π K → act z v = c • v := by
  refine ⟨ev.comp b.th, hu, ?_⟩
  obtain ⟨e, he⟩ := hkEv ℂ _ V ρ _ hI
  have hp : ∀ v : fixd ρ I, (v : V) ∈ fixd ρ K → (e (b.th z) v : V) ∈ fixd ρ K := by
    intro v hv
    refine (hs _).2 fun i j hij => ?_
    have h1 := congrArg e ((hkBern ℂ n _ _ b).2 z hz (Equiv.swap i j))
    rw [map_mul, map_mul, hb, he] at h1
    have h2 := LinearMap.congr_fun h1 v
    rw [Module.End.mul_apply, Module.End.mul_apply, (hs v).1 hv i j hij, map_smul] at h2
    exact h2
  have hc : ∃ c : ℂ, ∀ v : fixd ρ I, (v : V) ∈ fixd ρ K → e (b.th z) v = c • v := by
    by_cases h : ∃ u : fixd ρ I, (u : V) ∈ fixd ρ K ∧ (u : V) ≠ 0
    · obtain ⟨u, hu, hu0⟩ := h
      obtain ⟨c, hc⟩ := hl _ hu _ (hp u hu) hu0
      have hc' : e (b.th z) u = c • u := Subtype.ext hc
      refine ⟨c, fun v hv => ?_⟩
      obtain ⟨a, ha⟩ := hl _ hu _ hv hu0
      obtain rfl : v = a • u := Subtype.ext ha
      rw [map_smul, hc', smul_comm]
    · refine ⟨0, fun v hv => ?_⟩
      obtain rfl : v = 0 := Subtype.ext (by_contra fun h0 => h ⟨v, hv, h0⟩)
      rw [map_zero, smul_zero]
  obtain ⟨c, hc⟩ := hc
  refine ⟨c, fun y hy => ?_⟩
  have hsub : (⨆ f : {f : V →ₗ[ℂ] Y // ∀ g v, f (ρ g v) = π g (f v)}, (fixd ρ K).map f.1) ≤
      (Module.End.eigenspace (ev (b.th z)) c).map (fixd π I).subtype := by
    refine iSup_le ?_
    rintro ⟨f, hf⟩ _ ⟨v, hv, rfl⟩
    have hv' : v ∈ fixd ρ I := fixd_anti ρ hle hv
    refine ⟨⟨f v, fun u hu => by rw [← hf, hv' u hu]⟩, Module.End.mem_eigenspace_iff.2 (Subtype.ext ?_), rfl⟩
    rw [sphScalar_ev ρ π _ hI e he ev hev f hf _ ⟨v, hv'⟩ _ rfl, hc _ hv]
    exact map_smul f c v
  obtain ⟨y', hy', e'⟩ := hsub (hiso y hy)
  obtain rfl : y' = y := Subtype.ext e'
  exact Module.End.mem_eigenspace_iff.1 hy'

private theorem sphScalar_fin {W κ : Type} [AddCommGroup W] [Module ℂ W] (act : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ W)
    (a : κ → ℂ) (ha : ∀ i, a i ≠ 0) (u : κ → Module.End ℂ W) (hact : ∀ i, act (MvPolynomial.X i) = a i • u i)
    (z : MvPolynomial κ ℂ) (c : ℂ) :
    ∃ (act' : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ W) (F : MvPolynomial κ ℂ), (∀ i, act' (MvPolynomial.X i) = u i) ∧
      (∀ s : κ → ℂ, MvPolynomial.eval (fun i => a i * s i) z = c → MvPolynomial.eval s F = 0) ∧
      ∀ N : ℕ, act' (F ^ N) = (act z - algebraMap ℂ _ c) ^ N := by
  let up : MvPolynomial κ ℂ →ₐ[ℂ] MvPolynomial κ ℂ := MvPolynomial.aeval fun i => a i • MvPolynomial.X i
  let dn : MvPolynomial κ ℂ →ₐ[ℂ] MvPolynomial κ ℂ := MvPolynomial.aeval fun i => (a i)⁻¹ • MvPolynomial.X i
  have hud : dn.comp up = AlgHom.id ℂ _ := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp only [up, dn, AlgHom.comp_apply, MvPolynomial.aeval_X, map_smul, smul_smul, AlgHom.id_apply]
    rw [mul_inv_cancel₀ (ha i), one_smul]
  refine ⟨act.comp dn, up (z - algebraMap ℂ _ c), fun i => ?_, fun s hs => ?_, fun N => ?_⟩
  · simp only [dn, AlgHom.comp_apply, MvPolynomial.aeval_X, map_smul, hact, smul_smul]
    rw [inv_mul_cancel₀ (ha i), one_smul]
  · have h3 : (MvPolynomial.aeval s).comp up = MvPolynomial.aeval fun i => a i * s i := by
      refine MvPolynomial.algHom_ext fun i => ?_
      simp only [up, AlgHom.comp_apply, MvPolynomial.aeval_X, map_smul, smul_eq_mul]
    have h4 := AlgHom.congr_fun h3 (z - algebraMap ℂ _ c)
    rw [AlgHom.comp_apply, map_sub (MvPolynomial.aeval (R := ℂ) fun i => a i * s i), AlgHom.commutes,
      MvPolynomial.aeval_eq_eval, MvPolynomial.aeval_eq_eval, hs] at h4
    exact h4.trans (sub_self c)
  · rw [map_pow, AlgHom.comp_apply, ← AlgHom.comp_apply dn up, hud, AlgHom.id_apply, map_sub, AlgHom.commutes]

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem sphScalar_idx : (iwC k n ⊤).relIndex (KO k (Fin n)) ≠ 0 := by
  have ho : IsOpen (iwC k n ⊤ : Set (GL (Fin n) k)) :=
    Subgroup.isOpen_mono (H₁ := KOne k (Fin n)) (le_sup_left.trans le_sup_left) GlobalTheory.StepData.isOpen_KOne
  haveI : CompactSpace (KO k (Fin n)) := isCompact_iff_compactSpace.1 GlobalTheory.SplitFlip.isCompact_KO
  haveI := Subgroup.quotient_finite_of_isOpen ((iwC k n ⊤).subgroupOf (KO k (Fin n)))
    (ho.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

private theorem sphScalar_loc (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {Y : Type} [AddCommGroup Y] [Module ℂ Y] (π : Representation ℂ (GL (Fin n) k) Y)
    (σ : SmIrr (GL (Fin n) k)) (hs : IsoSum π ⊤ σ) (x : kˣ) (hx : IsUnif x)
    (z : MvPolynomial (Fin n) ℂ) (hz : z.IsSymmetric) :
    ∃ θ, IsTheta π ⊤ θ ∧ ∃ act : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Module.End ℂ (fixd π (iwC k n ⊤)),
      (∀ i : Fin n, act (MvPolynomial.X i) =
        ((resCard k : ℂ) ^ (i : ℕ)) • (θ (Pi.mulSingle i x) : Module.End ℂ (fixd π (iwC k n ⊤)))) ∧
      ∃ c : ℂ, ∀ v : fixd π (iwC k n ⊤), (v : Y) ∈ fixd π (KO k (Fin n)) → act z v = c • v := by
  have hI := (heckePairIwC k n ⊤).1
  have hle : iwC k n ⊤ ≤ KO k (Fin n) := (memIwC k n ⊤).2.1 ▸ iwahori_le_KO k (Fin n)
  have hq : IsUnit (resCard k : ℂ) := (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[k])).ne').isUnit
  have hreg : IsSMulRegular σ.V ((iwC k n ⊤).relIndex (KO k (Fin n)) : ℂ) :=
    smul_right_injective σ.V (Nat.cast_ne_zero.2 sphScalar_idx)
  refine (thetaEx k n ⊤ ℂ Y π hq).exists.elim fun θ hθ => ⟨θ, hθ, ?_⟩
  refine (bernHk k n ℂ x hx hq).elim fun b hb => ?_
  refine (hkEv ℂ _ Y π _ hI).elim fun ev hev => ?_
  have htie := thetaTie k n ℂ Y π x hx hq b ev θ hev hθ hb.2
  exact sphScalar_gen σ.ρ π _ _ hle hI b (fun w => pm k n w) hb.1 ev hev (sphEq k n ℂ σ.V σ.ρ hreg)
    (sphLine hBZ k n σ) (isoFix k n Y π σ _ GlobalTheory.SplitFlip.isCompact_KO hs) z hz _ htie

end Loc

theorem UpperTheory.V.Pa.Lev.sphScalar :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (π : Representation ℂ (GV n w) Y) (Θ), IsThetaQ π (fun _ => ⊤) Θ → ∀ (j : Fin q) (σ : SmIrr (GLw n (w j))), IsoSum (π.comp (atJ n w j)) ⊤ σ → ∀ (x : ((w j).adicCompletion L)ˣ), IsUnif x → ∀ (act : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Module.End ℂ (fixd π (UC n w fun _ => ⊤))), (∀ i : Fin n, act (MvPolynomial.X i) = ((qj w j : ℂ) ^ (i : ℕ)) • (Θ j (Pi.mulSingle i x) : Module.End ℂ _)) → ∀ (z : MvPolynomial (Fin n) ℂ) (c : ℂ), z.IsSymmetric → (∀ θ, IsTheta σ.ρ ⊤ θ → ∀ χ : (Fin n → ((w j).adicCompletion L)ˣ) →* ℂˣ, (⨅ t, Module.End.maxGenEigenspace (θ t : Module.End ℂ (fixd σ.ρ (iwC _ n ⊤))) (χ t : ℂ)) ≠ ⊥ → MvPolynomial.eval (fun i : Fin n => (qj w j : ℂ) ^ (i : ℕ) * (χ (Pi.mulSingle i x) : ℂ)) z = c) → ∀ m : fixd π (UC n w fun _ => ⊤), (m : Y) ∈ fixd (π.comp (atJ n w j)) (KO _ (Fin n)) → act z m = c • m := by
  intro hG hBZ L _ _ n q w Y _ _ π Θ hΘ j σ hs x hx act hact z c hz hc m hm
  have hq0 : (qj w j : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[(w j).adicCompletion L])).ne'
  obtain ⟨θY, hY, actY, haY, c', hc'⟩ := sphScalar_loc hBZ (π.comp (atJ n w j)) σ hs x hx z hz
  have hle : fixd π (UC n w fun _ => ⊤) ≤ fixd (π.comp (atJ n w j)) (iwC _ n ⊤) := by
    intro x hx u hu
    refine hx (atJ n w j u) fun j' _ => ?_
    by_cases h : j' = j
    · subst h
      simpa [atJ] using hu
    · have : atJ n w j u j' = 1 := Pi.mulSingle_eq_of_ne (M := fun j => GLw n (w j)) h u
      rw [this]
      exact (iwC _ n ⊤).one_mem
  have h1 : act z m = c' • m :=
    sphScalar_tr act actY (Submodule.inclusion hle) (Submodule.inclusion_injective hle) _ _ _ hact haY
      (fun a v => Subtype.ext (thetaLoc L n q w ℂ Y π _ Θ hΘ j θY hY _ v _ rfl)) z c' m (hc' _ hm)
  obtain ⟨act', F, h2, h3, h4⟩ := sphScalar_fin act (fun i : Fin n => (qj w j : ℂ) ^ (i : ℕ))
    (fun _ => pow_ne_zero _ hq0) _ hact z c
  have h5 := nilKill hG hBZ L n q w Y π _ Θ hΘ j σ hs (Fin n) (fun i => Pi.mulSingle i x) act' h2 F
    fun θ hθ χ hχ => h3 _ (hc θ hθ χ hχ)
  exact sphScalar_nil _ c c' _ m h1 ((h4 _).symm.trans h5)
