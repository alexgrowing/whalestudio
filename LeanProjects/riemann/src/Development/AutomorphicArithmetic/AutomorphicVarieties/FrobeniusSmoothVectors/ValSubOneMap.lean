import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrMu
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LcMatrix
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCorrect
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrNorm

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O] [IsLocalRing O] {C' : Type} [CommRing C'] [Algebra O C'] [IsCO O C']
  {C'' : Type} [CommRing C''] [Algebra O C''] [IsCO O C'']

private theorem mem_max_iff (q : C' →ₐ[O] C'') (x : C') : q x ∈ maximalIdeal C'' ↔ x ∈ maximalIdeal C' := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

private theorem adicCont_map {Γ : Type} [TopologicalSpace Γ] (q : C' →ₐ[O] C'') {f : Γ → C'}
    (hf : AdicCont (maximalIdeal C') f) : AdicCont (maximalIdeal C'') fun g => q (f g) := by
  intro N
  have hle : maximalIdeal C' ^ N ≤ (maximalIdeal C'' ^ N).comap (q : C' →+* C'') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    exact (mem_max_iff q y).2 hy
  exact (hf N).comp (Ideal.quotientMap _ (q : C' →+* C'') hle)

private theorem map_sgnAct {m : ℕ} {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A') (s : ℤˣ)
    (g : GL (Fin m) A) :
    GeneralLinearGroup.map f (sgnAct m A s g) = sgnAct m A' s (GeneralLinearGroup.map f g) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [sgnAct_one, sgnAct_one]
  · rw [sgnAct_neg_one, sgnAct_neg_one, map_theta]

private theorem val_sub_one_map {m : ℕ} {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A')
    (g : GL (Fin m) A) (i j : Fin m) :
    (((GeneralLinearGroup.map f g : GL (Fin m) A') : Matrix (Fin m) (Fin m) A') - 1) i j =
      f (((g : Matrix (Fin m) (Fin m) A) - 1) i j) := by
  have e : ((GeneralLinearGroup.map f g : GL (Fin m) A') : Matrix (Fin m) (Fin m) A') - 1 =
      f.mapMatrix ((g : Matrix (Fin m) (Fin m) A) - 1) := by
    rw [map_sub, map_one]
    rfl
  rw [e]
  rfl

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
  {R : Type} [CommRing R] [Algebra O R] {B : Box F n R}

private noncomputable def push (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R) (D : SetLift (p''.comp q) B) :
    SetLift p'' B where
  r s := GeneralLinearGroup.map (q : C' →+* C'') (D.r s)
  r_cont i j := adicCont_map q (D.r_cont i j)
  r_map s := D.r_map s
  g v := GeneralLinearGroup.map (q : C' →+* C'') (D.g v)
  g_map v := D.g_map v
  t v s := GeneralLinearGroup.map (q : C' →+* C'') (D.t v s)
  t_cont v i j := adicCont_map q (D.t_cont v i j)
  t_tri v s i j h := (congrArg q (D.t_tri v s i j h)).trans (map_zero q)
  t_map v s := D.t_map v s

private theorem push_om (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R) (D : SetLift (p''.comp q) B)
    (x : F.Γ × F.Γ) (i j : Fin n) : (push q p'' D).om x i j = q (D.om x i j) := by
  refine Eq.trans ?_ (val_sub_one_map (q : C' →+* C'') _ i j)
  rw [map_mul, map_mul, map_inv, map_sgnAct]
  rfl

private theorem push_a (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R) (D : SetLift (p''.comp q) B)
    (v : F.V) (s : F.Gv v) (i j : Fin n) : (push q p'' D).a v s i j = q (D.a v s i j) := by
  refine Eq.trans ?_ (val_sub_one_map (q : C' →+* C'') _ i j)
  rw [map_mul, map_inv, map_mul, map_mul, map_inv]
  rfl

end SlopeTestRemainingChoices

theorem UpperTheory.V.Fr.pr_obs :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : NRep F n R) (B : Box F n R), ρ.Univ O → B.Of ρ → B.Cont (maximalIdeal R) → (ρ.bar O).Good → ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (p : C' →ₐ[O] R) (D : SetLift p B) (u : RingHom.ker p →ₗ[O] ResidueField O), maximalIdeal C' * RingHom.ker p = ⊥ → D.co u ∈ continuousCoboundaries2 F.loc (B.bar O).ad (B.bar O).b → ∀ (C'' : Type) [CommRing C''] [Algebra O C''] [IsCO O C''] (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R), p''.comp q = p → Function.Surjective q → (∀ y : RingHom.ker p, u y = 0 → q y = 0) → ∃ s : R →ₐ[O] C'', p''.comp s = AlgHom.id O R := by
  intro l _ k _ _ F C₀ n hF O _ _ R _ _ _ ρ B hU hOf hC hG C' _ _ _ p D u hsm hco C'' _ _ _ q p'' hpq hq hu
  subst hpq
  have hK : RingHom.ker (p''.comp q) ≤ maximalIdeal C' := fun y hy => by
    rw [← mem_max_iff (p''.comp q), (RingHom.mem_ker).1 hy]
    exact zero_mem _
  obtain ⟨μ, hμ, hμu, hμq⟩ := pr_mu O C' C'' _ q u hsm hK hq hu
  obtain ⟨hom, ha, -, -⟩ := pr_omk hF O C' R (p''.comp q) B D hsm
  obtain ⟨β, Y, hβ, h1, h2⟩ := hco
  have hev : ∀ y ∈ RingHom.ker (p''.comp q), q y = μ (evK _ u y) := fun y hy => by
    rw [evK_of_mem u hy, hμu]
  have hp0 : ∀ c, p'' (μ c) = 0 := fun c => by
    obtain ⟨y, hy⟩ := hμq c
    rw [hy]
    exact y.2
  obtain ⟨B', hB'c, hB'm, -⟩ := pr_correct hF O C'' R p'' B (push q p'' D) μ hμ hp0 β Y (D.co u).2 hβ
    (fun x => by
      rw [← h1]
      ext i j
      rw [push_om, hev _ (hom x i j)]
      rfl)
    (fun v s => by
      ext i j
      rw [push_a, hev _ (ha v s i j)]
      rfl) h2
  have hsm'' : maximalIdeal C'' * RingHom.ker p'' = ⊥ := by
    refine le_bot_iff.1 (Ideal.mul_le.2 fun a ha' b hb => ?_)
    obtain ⟨a, rfl⟩ := hq a
    obtain ⟨b, rfl⟩ := hq b
    have hab : a * b ∈ maximalIdeal C' * RingHom.ker (p''.comp q) :=
      Ideal.mul_mem_mul ((mem_max_iff q a).1 ha') hb
    rw [hsm, Ideal.mem_bot] at hab
    rw [← map_mul, hab, map_zero]
    exact zero_mem _
  obtain ⟨-, ρ', -, hρm, hρc, -, -⟩ := pr_norm hF O C'' R p'' ρ B' hsm'' hG (hB'm ▸ hOf) hB'c
  have hbar : ρ'.bar O = ρ.bar O := by
    have e : (res O C'' : C'' →+* ResidueField O) =
        (res O R : R →+* ResidueField O).comp (p'' : C'' →+* R) :=
      RingHom.ext fun x => (res_map p'' x).symm
    show ρ'.map _ = ρ.map _
    rw [e, ← NRep.map_map, hρm]
  obtain ⟨g, hg, -⟩ := hU.univ C'' ρ' hρc hbar
  obtain ⟨g', -, hg'⟩ := hU.univ R ρ hU.cont rfl
  refine ⟨g, (hg' _ ?_).trans (hg' _ rfl).symm⟩
  show ρ.map ((p'' : C'' →+* R).comp (g : R →+* C'')) = ρ
  rw [← NRep.map_map, hg, hρm]
