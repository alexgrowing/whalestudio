import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.EqOfTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PropCker
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqMult
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqEmbed

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Hi.OrdB

open GlobalTheory.PRep

section General

variable {G V : Type} [CommGroup G] [AddCommGroup V] [Module ℂ V]

private theorem pow_comm (ρ : Representation ℂ G V) (t g : G) (c : ℂ) (m : ℕ) (v : V) :
    ((ρ t - c • (1 : Module.End ℂ V)) ^ m) (ρ g v) = ρ g (((ρ t - c • (1 : Module.End ℂ V)) ^ m) v) := by
  have hc : Commute (ρ t) (ρ g) := by
    show ρ t * ρ g = ρ g * ρ t
    rw [← map_mul, ← map_mul, mul_comm]
  have h2 : Commute (ρ t - c • (1 : Module.End ℂ V)) (ρ g) :=
    hc.sub_left ((Commute.one_left _).smul_left c)
  exact LinearMap.congr_fun ((h2.pow_left m).eq) v

private theorem pow_mem (ρ : Representation ℂ G V) (N : Subrepresentation ρ) (t : G) (c : ℂ) (m : ℕ)
    (v : V) (hv : v ∈ N.toSubmodule) : ((ρ t - c • (1 : Module.End ℂ V)) ^ m) v ∈ N.toSubmodule := by
  induction m with
  | zero => simpa using hv
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact N.toSubmodule.sub_mem (N.apply_mem_toSubmodule t ih) (N.toSubmodule.smul_mem c ih)

private theorem exists_nil {ρ : Representation ℂ G V} (hl : HasFiniteLength ρ) {x : V} (hx : x ≠ 0) :
    ∃ N : Subrepresentation ρ, N ≠ ⊤ ∧ ∀ (t : G) (c : ℂ), ρ t x = c • x →
      ∃ m : ℕ, ∀ v, ((ρ t - c • (1 : Module.End ℂ V)) ^ m) v ∈ N.toSubmodule := by
  have hwf := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
  obtain ⟨N, hxN, hmax⟩ := (wellFounded_gt (α := Subrepresentation ρ)).has_min
    {N | x ∉ N.toSubmodule} ⟨⊥, fun h => hx ((Submodule.mem_bot ℂ).1 h)⟩
  have hxN' : x ∉ N.toSubmodule := hxN
  refine ⟨N, fun h => hxN' (by rw [h]; exact Submodule.mem_top), fun t c hx1 => ?_⟩
  obtain ⟨E, hE⟩ : ∃ E : Module.End ℂ V, E = ρ t - c • (1 : Module.End ℂ V) := ⟨_, rfl⟩
  have hc : ∀ m g w, (E ^ m) (ρ g w) = ρ g ((E ^ m) w) := by
    subst hE
    exact fun m g w => pow_comm ρ t g c m w
  have hm : ∀ m w, w ∈ N.toSubmodule → (E ^ m) w ∈ N.toSubmodule := by
    subst hE
    exact fun m w hw => pow_mem ρ N t c m w hw
  have hEx : E x = 0 := by
    rw [hE, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hx1, sub_self]
  rw [← hE]
  let M : ℕ →o Subrepresentation ρ :=
    ⟨fun j => ⟨N.toSubmodule.comap (E ^ j), fun g v hv => by
      show (E ^ j) (ρ g v) ∈ N.toSubmodule
      rw [hc]
      exact N.apply_mem_toSubmodule g hv⟩, fun i j hij v hv => by
      show (E ^ j) v ∈ N.toSubmodule
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
      rw [add_comm, pow_add, Module.End.mul_apply]
      exact hm d _ hv⟩
  obtain ⟨J, hJ⟩ := WellFoundedGT.monotone_chain_condition M
  refine ⟨J + 1, fun v => ?_⟩
  by_contra hv
  let L : Subrepresentation ρ := ⟨N.toSubmodule ⊔ LinearMap.range (E ^ (J + 1)), fun g w hw => by
    obtain ⟨n, hn, y, ⟨u, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hw
    rw [map_add, ← hc]
    exact Submodule.add_mem_sup (N.apply_mem_toSubmodule g hn) ⟨ρ g u, rfl⟩⟩
  have hlt : N < L := lt_of_le_of_ne (le_sup_left : N.toSubmodule ≤ _) (fun h => hv (by
    have h5 : (E ^ (J + 1)) v ∈ L.toSubmodule := Submodule.mem_sup_right ⟨v, rfl⟩
    rw [← h] at h5
    exact h5))
  have hxL : x ∈ L.toSubmodule := by
    by_contra hxL
    exact hmax L hxL hlt
  obtain ⟨n, hn, y, ⟨u, rfl⟩, hxe⟩ := Submodule.mem_sup.1 hxL
  have h1 : (E ^ (J + 1)) x = 0 := by
    rw [pow_succ, Module.End.mul_apply, hEx, map_zero]
  have h2 : (E ^ (J + 1)) ((E ^ (J + 1)) u) ∈ N.toSubmodule := by
    have h6 := congrArg (E ^ (J + 1)) hxe
    rw [map_add, h1] at h6
    rw [eq_neg_of_add_eq_zero_right h6]
    exact N.toSubmodule.neg_mem (hm _ n hn)
  have h3 : u ∈ (M (2 * J + 2)).toSubmodule := by
    show (E ^ (2 * J + 2)) u ∈ N.toSubmodule
    rw [show 2 * J + 2 = (J + 1) + (J + 1) by omega, pow_add, Module.End.mul_apply]
    exact h2
  rw [← hJ (2 * J + 2) (by omega)] at h3
  change (E ^ J) u ∈ N.toSubmodule at h3
  have h4 : (E ^ (J + 1)) u ∈ N.toSubmodule := by
    rw [pow_succ', Module.End.mul_apply]
    simpa using hm 1 _ h3
  exact hxN' (hxe ▸ N.toSubmodule.add_mem hn h4)

private theorem pow_eig {f : Module.End ℂ V} {v : V} {a : ℂ} (h : f v = a • v) (c : ℂ) (m : ℕ) :
    ((f - c • (1 : Module.End ℂ V)) ^ m) v = (a - c) ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, h, pow_succ, mul_smul, sub_smul]
    rfl

private theorem eq_of_gen {f : Module.End ℂ V} {v : V} {a c : ℂ} (h : f v = a • v) (h0 : v ≠ 0)
    (hv : v ∈ f.maxGenEigenspace c) : a = c := by
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
  rw [pow_eig h] at hm
  exact sub_eq_zero.1 (pow_eq_zero_iff'.1 ((smul_eq_zero.1 hm).resolve_right h0)).1

private theorem exists_eig [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (E : Submodule ℂ V) (hE0 : E ≠ ⊥)
    (hE : ∀ t, ∀ v ∈ E, ρ t v ∈ E) : ∃ χ : G →* ℂˣ, ∃ v ∈ E, v ≠ 0 ∧ ∀ t, ρ t v = (χ t : ℂ) • v := by
  obtain ⟨S, ⟨hS0, hSE, hS⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ V)).has_min
    {S | S ≠ ⊥ ∧ S ≤ E ∧ ∀ t, ∀ v ∈ S, ρ t v ∈ S} ⟨E, hE0, le_rfl, hE⟩
  have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS0
  have key : ∀ t, ∃ c : ℂ, ∀ v ∈ S, ρ t v = c • v := fun t => by
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((ρ t).restrict (hS t))
    obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
    have hw1 : ρ t w = c • (w : V) := congrArg Subtype.val hw.apply_eq_smul
    refine ⟨c, fun v hv => ?_⟩
    have h1 : S ⊓ Module.End.eigenspace (ρ t) c = S := by
      by_contra hne
      refine hmin _ ⟨?_, inf_le_left.trans hSE, ?_⟩ (lt_of_le_of_ne inf_le_left hne)
      · exact (Submodule.ne_bot_iff _).2 ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩,
          fun h => hw.2 (Subtype.ext h)⟩
      · rintro s x ⟨hx, hx'⟩
        refine ⟨hS s x hx, Module.End.mem_eigenspace_iff.2 ?_⟩
        rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul,
          Module.End.mul_apply, Module.End.mem_eigenspace_iff.1 hx', map_smul]
    rw [← h1] at hv
    exact Module.End.mem_eigenspace_iff.1 hv.2
  choose c hc using key
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hS0
  let c' : G →* ℂ :=
    { toFun := c
      map_one' := by
        have := hc 1 v hv
        rw [map_one, Module.End.one_apply] at this
        exact smul_left_injective ℂ hv0 (this.symm.trans (one_smul _ _).symm)
      map_mul' := fun s t => by
        have := hc (s * t) v hv
        rw [map_mul, Module.End.mul_apply, hc t v hv, map_smul, hc s v hv, smul_smul, mul_comm] at this
        exact smul_left_injective ℂ hv0 this.symm }
  exact ⟨c'.toHomUnits, v, hSE hv, hv0, fun t => hc t v hv⟩

private theorem le_gen [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (E : Submodule ℂ V)
    (hE : ∀ t, ∀ v ∈ E, ρ t v ∈ E) (μ : G →* ℂˣ)
    (h : ∀ χ : G →* ℂˣ, ∀ v ∈ E, v ≠ 0 → (∀ t, ρ t v = (χ t : ℂ) • v) → χ = μ) (t : G) :
    E ≤ Module.End.maxGenEigenspace (ρ t) (μ t : ℂ) := by
  rw [Submodule.eq_iSup_inf_genEigenspace (p := E) (f := ρ t) ⊤ (hE t)
    (Module.End.iSup_maxGenEigenspace_eq_top (ρ t))]
  refine iSup_le fun c => ?_
  by_cases h0 : E ⊓ Module.End.genEigenspace (ρ t) c ⊤ = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨χ, v, hv, hv0, hχ⟩ := exists_eig ρ _ h0 fun s v hv => ⟨hE s v hv.1, by
    obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv.2
    exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨m, by rw [pow_comm, hm, map_zero]⟩⟩
  rw [← h χ v hv.1 hv0 hχ, eq_of_gen (hχ t) hv0 hv.2]
  exact inf_le_right

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace.SeparableSpace G]

private theorem exists_form {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ)
    {x : V} (hx : x ≠ 0) : ∃ μ : G →* ℂˣ, IsSmoothChar μ ∧ (∀ (t : G) (c : ℂ), ρ t x = c • x → (μ t : ℂ) = c) ∧
      ∃ l : V →ₗ[ℂ] ℂ, l ≠ 0 ∧ ∀ g v, l (ρ g v) = (μ g : ℂ) * l v := by
  obtain ⟨N, hNtop, hnil⟩ := exists_nil hl hx
  have hwf := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
  obtain ⟨P, ⟨hNP, hPtop⟩, hPmax⟩ := (wellFounded_gt (α := Subrepresentation ρ)).has_min
    {P | N ≤ P ∧ P ≠ ⊤} ⟨N, le_rfl, hNtop⟩
  have hcov : P ⋖ ⊤ := covBy_iff_lt_and_eq_or_eq.2 ⟨lt_top_iff_ne_top.2 hPtop, fun c hPc _ => by
    by_cases hc : c = ⊤
    · exact Or.inr hc
    · exact Or.inl (by_contra fun hne => hPmax c ⟨hNP.trans hPc, hc⟩ (lt_of_le_of_ne hPc (Ne.symm hne)))⟩
  have hirr := isIrreducible_subQuot hcov
  have hsub : IsSubquotient (subQuot ⊤ P) ρ :=
    ⟨⊤, ⟨Submodule.mkQ _, fun g => LinearMap.ext fun w => rfl⟩, Submodule.mkQ_surjective _⟩
  have hsm := hsub.isSmooth hρ
  obtain ⟨μ, hμ⟩ := GlobalTheory.TorusEigenform.exists_char_of_isIrreducible hsm hirr
  let π0 : V →ₗ[ℂ] (↥(⊤ : Subrepresentation ρ).toSubmodule ⧸
      Submodule.comap (⊤ : Subrepresentation ρ).toSubmodule.subtype P.toSubmodule) :=
    (Submodule.mkQ _) ∘ₗ (LinearMap.codRestrict _ LinearMap.id fun v => Submodule.mem_top)
  have hπ0 : ∀ g v, π0 (ρ g v) = (μ g : ℂ) • π0 v := fun g v => by
    rw [← hμ]
    rfl
  have hz : ∀ v, π0 v = 0 ↔ v ∈ P.toSubmodule := fun v => by
    show Submodule.Quotient.mk (⟨v, Submodule.mem_top⟩ : ↥(⊤ : Subrepresentation ρ).toSubmodule) = 0 ↔ _
    exact Submodule.Quotient.mk_eq_zero _
  obtain ⟨v0, hv0⟩ : ∃ v, v ∉ P.toSubmodule := by
    by_contra hall
    push_neg at hall
    exact hPtop (Subrepresentation.ext (eq_top_iff.2 fun v _ => hall v))
  have hq0 : π0 v0 ≠ 0 := fun h => hv0 ((hz v0).1 h)
  have hpow : ∀ (t : G) (c : ℂ) (m : ℕ) (v : V),
      π0 (((ρ t - c • (1 : Module.End ℂ V)) ^ m) v) = (((μ t : ℂ) - c) ^ m) • π0 v := by
    intro t c m
    induction m with
    | zero => intro v; simp
    | succ m ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, map_sub, map_smul, hπ0, ih, pow_succ', mul_smul, sub_smul]
  refine ⟨μ, ?_, ?_, ?_⟩
  · have hker : (μ.ker : Set G) = {g | subQuot ⊤ P g (π0 v0) = π0 v0} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_setOf_eq, hμ]
      constructor
      · intro h
        rw [h]
        simp
      · intro h
        have h7 : ((μ g : ℂ) - 1) • π0 v0 = 0 := by rw [sub_smul, h, one_smul, sub_self]
        rcases smul_eq_zero.1 h7 with h' | h'
        · exact Units.ext (by simpa [sub_eq_zero] using h')
        · exact absurd h' hq0
    show IsOpen (μ.ker : Set G)
    rw [hker]
    exact hsm _
  · intro t c htc
    obtain ⟨m, hm⟩ := hnil t c htc
    have h8 := hpow t c m v0
    rw [(hz _).2 (hNP (hm v0))] at h8
    rcases smul_eq_zero.1 h8.symm with h' | h'
    · exact sub_eq_zero.1 (pow_eq_zero_iff'.1 h').1
    · exact absurd h' hq0
  · obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ _, φ (π0 v0) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hq0 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hall)
    refine ⟨φ ∘ₗ π0, fun h => hφ (by simpa using LinearMap.congr_fun h v0), fun g v => ?_⟩
    simp only [LinearMap.comp_apply, hπ0, map_smul, smul_eq_mul]

end General

section Abs

variable {G M : Type} [Group G] (I : Iwa G) [AddCommGroup M] [Module ℂ M] (π : Representation ℂ G M) (c : ℕ)
  (φ : I.T →* ℂˣ)

private theorem eig_le (hφ : ∀ t : I.T, (t : G) ∈ I.Tc c → φ t = 1) : I.eig π c φ ≤ fixd π (I.I1 c) := by
  intro v hv
  obtain ⟨hN, hNm, hT⟩ := hv
  show ∀ g ∈ I.I1 c, π g v = v
  intro g hg
  obtain ⟨x, hx, t, ht, y, hy, rfl⟩ := ((iwMem G I c g).2.1).1 hg
  have htT : t ∈ I.T := I.Tc_le c ht
  have h1 := hT ⟨t, htT⟩
  rw [hφ ⟨t, htT⟩ ht, inv_one, Units.val_one, one_smul] at h1
  have h2 : π t v = v := h1
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hNm y hy, h2]
  exact hN x hx

private theorem inv_stab (hφ : ∀ t : I.T, (t : G) ∈ I.Tc c → φ t = 1) {a : G} (ha : a ∈ I.P) {v : M}
    (hv : v ∈ ⨅ j : ℕ, (I.eig π c φ).map (I.uOp π I.z ^ j)) :
    I.uOp π a v ∈ ⨅ j : ℕ, (I.eig π c φ).map (I.uOp π I.z ^ j) := by
  have st := ((uOpLevel G I ℂ M π c).2.2 φ hφ).1
  have key : ∀ (j : ℕ), ∀ w ∈ I.eig π c φ, I.uOp π a ((I.uOp π I.z ^ j) w) = (I.uOp π I.z ^ j) (I.uOp π a w) := by
    intro j
    induction j with
    | zero => intro w _; simp
    | succ j ih =>
      intro w hw
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih _ (st _ I.z_mem w hw),
        (uOpMul G I ℂ M π _ _ ha I.z_mem w hw.1).2.1, (uOpMul G I ℂ M π _ _ I.z_mem ha w hw.1).2.1,
        I.comm a (I.P_le a ha) I.z (I.P_le _ I.z_mem)]
  refine (Submodule.mem_iInf _).2 fun j => ?_
  obtain ⟨w, hw, rfl⟩ := (Submodule.mem_iInf _).1 hv j
  exact ⟨_, st a ha w hw, (key j w hw).symm⟩

private theorem inv_inj (hφ : ∀ t : I.T, (t : G) ∈ I.Tc c → φ t = 1) (hs : I.Smooth π)
    [FiniteDimensional ℂ (fixd π (I.I1 c))] {v : M}
    (hv : v ∈ ⨅ j : ℕ, (I.eig π c φ).map (I.uOp π I.z ^ j)) (h0 : v ∈ I.jacKer π) : v = 0 := by
  have hE5 := eig_le I π c φ hφ
  haveI : FiniteDimensional ℂ (I.eig π c φ) := Submodule.finiteDimensional_of_le hE5
  have hst : ∀ w ∈ I.eig π c φ, I.uOp π I.z w ∈ I.eig π c φ :=
    ((uOpLevel G I ℂ M π c).2.2 φ hφ).1 I.z I.z_mem
  let f : I.eig π c φ →ₗ[ℂ] I.eig π c φ := (I.uOp π I.z).restrict hst
  have hvE : v ∈ I.eig π c φ := by
    obtain ⟨w, hw, hwv⟩ := (Submodule.mem_iInf _).1 hv 0
    rw [pow_zero, Module.End.one_apply] at hwv
    exact hwv ▸ hw
  have hvE' := hvE
  obtain ⟨hvN, -⟩ := hvE'
  obtain ⟨j, hj⟩ := (propCker G I ℂ M π hs v hvN).1 h0
  have key := LinearMap.isCompl_iSup_ker_pow_iInf_range_pow f
  have h1 : (⟨v, hvE⟩ : I.eig π c φ) ∈ ⨆ n, (f ^ n).ker := Submodule.mem_iSup_of_mem j (by
    rw [LinearMap.mem_ker, Module.End.pow_restrict, LinearMap.restrict_apply]
    exact Subtype.ext hj)
  have h2 : (⟨v, hvE⟩ : I.eig π c φ) ∈ ⨅ n, (f ^ n).range := (Submodule.mem_iInf _).2 fun n => by
    obtain ⟨w, hw, hwv⟩ := (Submodule.mem_iInf _).1 hv n
    refine ⟨⟨w, hw⟩, ?_⟩
    rw [Module.End.pow_restrict, LinearMap.restrict_apply]
    exact Subtype.ext hwv
  have h3 : (⟨v, hvE⟩ : I.eig π c φ) ∈ (⨆ n, (f ^ n).ker) ⊓ (⨅ n, (f ^ n).range) :=
    Submodule.mem_inf.2 ⟨h1, h2⟩
  rw [key.inf_eq_bot] at h3
  exact congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h3)

end Abs

section Num

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem tc_single (ψ : Fin n → kˣ →* ℂˣ) (i : Fin n) (x : kˣ) : torusChar ψ (Pi.mulSingle i x) = ψ i x := by
  rw [torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, map_one])
    (fun h => absurd (Finset.mem_univ i) h), Pi.mulSingle_eq_same]

private theorem num (ω : Fin n → kˣ →* ℂˣ) {j : ℕ} (hj : j ≤ n) :
    ((Nat.card 𝓀[k] ^ (j * (n - j)) : ℕ) : ℂ) *
      ((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) fun i => unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ) *
        (torusChar (fun i => ω i * absPow k (((n : ℂ) - 1) / 2))
          (fun i => unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ)) = psEig ω j := by
  have hQ0 : (Nat.card 𝓀[k] : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have harg : (Nat.card 𝓀[k] : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_pos.ne
  have hu : ∀ s : ℂ, ((absPow k s (unif k) : ℂˣ) : ℂ) = ((Nat.card 𝓀[k] : ℂ) ^ s)⁻¹ := by
    intro s
    rw [val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, ord_eq_one UpperTheory.V.Hi.GlAx.unif_spec]
    simp only [Complex.ofReal_zpow, zpow_neg, zpow_one, Complex.ofReal_inv, Complex.ofReal_natCast, resCard]
    exact Complex.inv_cpow _ _ harg
  have he : ∀ (s : ℂ) (i : Fin n), ((absPow k s (unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂˣ) : ℂ)
      = if (i : ℕ) < j then ((Nat.card 𝓀[k] : ℂ) ^ s)⁻¹ else 1 := by
    intro s i
    split_ifs <;> simp [hu]
  have hω : ∀ i : Fin n, ((ω i (unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂˣ) : ℂ)
      = if (i : ℕ) < j then ((ω i (unif k) : ℂˣ) : ℂ) else 1 := by
    intro i
    split_ifs <;> simp
  have hdet : ∀ (t : Fin n → kˣ) (i : Fin n),
      Matrix.GeneralLinearGroup.det ((leviTorus k (Fin n) t) i) = t i := fun t i => by
    have h := congrFun ((leviTorus k (Fin n)).symm_apply_apply t) i
    exact h
  have alg : ∀ (a b w : ℂ) (i : ℕ), i < n → a + b = (n : ℂ) - 1 - (i : ℂ) →
      ((Nat.card 𝓀[k] : ℂ) ^ a)⁻¹ * (w * ((Nat.card 𝓀[k] : ℂ) ^ b)⁻¹)
        = w * ((Nat.card 𝓀[k] : ℂ) ^ i / (Nat.card 𝓀[k] : ℂ) ^ (n - 1)) := by
    intro a b w i hi hab
    have h1 : (Nat.card 𝓀[k] : ℂ) ^ a * (Nat.card 𝓀[k] : ℂ) ^ b
        = (Nat.card 𝓀[k] : ℂ) ^ (n - 1) / (Nat.card 𝓀[k] : ℂ) ^ i := by
      rw [← Complex.cpow_add _ _ hQ0, hab, Complex.cpow_sub _ _ hQ0, Complex.cpow_natCast,
        ← Complex.cpow_natCast _ (n - 1), Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    rw [show ((Nat.card 𝓀[k] : ℂ) ^ a)⁻¹ * (w * ((Nat.card 𝓀[k] : ℂ) ^ b)⁻¹)
        = w * ((Nat.card 𝓀[k] : ℂ) ^ a * (Nat.card 𝓀[k] : ℂ) ^ b)⁻¹ by ring, h1, inv_div]
  have hsum : ∀ f : ℕ → ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), f i
      = ∑ i ∈ Finset.range j, f i := by
    intro f
    rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun i => if i < j then f i else 0) n]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [Finset.sum_range_add, Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.1 hi)),
      Finset.sum_eq_zero (fun x _ => if_neg (by omega)), add_zero]
  have hsumid : ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), (i : ℕ)
      = ∑ i ∈ Finset.range j, i := hsum (fun i => i)
  have hcard : (Finset.univ.filter (fun i : Fin n => (i : ℕ) < j)).card = j := by
    rw [Finset.card_eq_sum_ones, hsum (fun _ => 1)]
    simp
  have hexp : j * (n - j) + (∑ i ∈ Finset.range j, i) + (∑ i ∈ Finset.range j, i) = (n - 1) * j := by
    have h2 := Finset.sum_range_id_mul_two j
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    rcases j with _ | j
    · simp
    · rw [show j + 1 + d - (j + 1) = d by omega, show j + 1 + d - 1 = j + d by omega] at *
      rw [show j + 1 - 1 = j by omega] at h2
      nlinarith [h2]
  rw [deltaHalf_apply, torusChar_apply, Units.coe_prod, Units.coe_prod]
  simp only [hdet, modExp_fin _ (fun _ => Fintype.card_unit), MonoidHom.mul_apply, Units.val_mul, he, hω]
  rw [← Finset.prod_mul_distrib]
  have hprod : (∏ x : Fin n, (if (x : ℕ) < j then ((Nat.card 𝓀[k] : ℂ) ^
        ((((n : ℤ) - 1 - 2 * ((x : ℕ) : ℤ) : ℤ) : ℂ) / 2))⁻¹ else 1) *
        ((if (x : ℕ) < j then ((ω x (unif k) : ℂˣ) : ℂ) else 1) *
          if (x : ℕ) < j then ((Nat.card 𝓀[k] : ℂ) ^ (((n : ℂ) - 1) / 2))⁻¹ else 1))
      = ∏ x : Fin n, if (x : ℕ) < j then ((ω x (unif k) : ℂˣ) : ℂ) *
          ((Nat.card 𝓀[k] : ℂ) ^ (x : ℕ) / (Nat.card 𝓀[k] : ℂ) ^ (n - 1)) else 1 :=
    Finset.prod_congr rfl fun x _ => by
      split_ifs with h
      · exact alg _ _ _ x x.isLt (by push_cast; ring)
      · simp
  rw [hprod, ← Finset.prod_filter]
  unfold psEig
  rw [Nat.cast_pow, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_div_distrib,
    Finset.prod_inv_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, hcard, hsumid]
  rw [show ((Nat.card 𝓀[k] : ℂ) ^ (n - 1)) ^ j = (Nat.card 𝓀[k] : ℂ) ^ (j * (n - j)) *
      (Nat.card 𝓀[k] : ℂ) ^ (∑ i ∈ Finset.range j, i) * (Nat.card 𝓀[k] : ℂ) ^ (∑ i ∈ Finset.range j, i) by
    rw [← pow_mul, ← pow_add, ← pow_add, hexp]]
  field_simp

end Num

end UpperTheory.V.Hi.OrdB

open GlobalTheory.PRep in
theorem UpperTheory.V.Hi.ordB :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), GlobalTheory.PRep.IsSmooth π → π.IsIrreducible → ∀ (c : ℕ) (φ : (glIwa k n).T →* ℂˣ), (∀ i (y : Uo k), (y : kˣ) ∈ Uc k (c + 1) → φ (eT k n i y) = 1) → Distinct φ → invPart π c φ ≠ ⊥ → ∃ ω : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ IsInvOn φ ω ∧ Nonempty (π.Equiv (PS ω)) ∧ Module.finrank ℂ (invPart π c φ) = 1 ∧ ∀ v ∈ invPart π c φ, ∀ j ≤ n, (glIwa k n).uOp π (al k n j) v = psEig ω j • v := by
  intro H k _ _ _ _ n V _ _ π hπ hirr c φ hφ0 hD hne
  obtain ⟨hker, hsm, hI, -, -, -, -, hidx, -, hT⟩ := glBridge k n V π
  have hφ : ∀ t : (glIwa k n).T, (t : GL (Fin n) k) ∈ (glIwa k n).Tc c → φ t = 1 := fun t ht => by
    obtain ⟨y, hy, hy'⟩ := hT t
    have e : (t : GL (Fin n) k) ∈ φ.ker.map (glIwa k n).T.subtype := by
      rw [hy]
      refine list_prod_mem fun x hx => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact ⟨eT k n i (y i), hφ0 i _ (hy' c ht i), rfl⟩
    obtain ⟨s, hs, e⟩ := e
    exact (Subtype.ext e : s = t) ▸ hs
  haveI : FiniteDimensional ℂ (fixd π ((glIwa k n).I1 c)) := by
    have hfix : fixd π ((glIwa k n).I1 c) = fixed π ((glIwa k n).I1 c) := by
      ext v
      exact ⟨fun h u => by simpa using h u u.2, fun h u hu => by simpa using h ⟨u, hu⟩⟩
    rw [hfix]
    exact ((H.loc.bz k).1 _ V π hπ hirr).2 _ (hI c).1 (hI c).2
  let p : V →ₗ[ℂ] Jacquet π (unipB k (Fin n)) := Submodule.mkQ _
  have hinj : ∀ v ∈ invPart π c φ, p v = 0 → v = 0 := fun v hv h =>
    OrdB.inv_inj _ π c φ hφ (hsm hπ) hv (hker ▸ (Submodule.Quotient.mk_eq_zero _).1 h)
  have heig : invPart π c φ ≤ (glIwa k n).eig π c φ := fun v hv => by simpa using (Submodule.mem_iInf _).1 hv 0
  have hp : ∀ t v, jacB π t (p v) =
      (((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) t))⁻¹ : ℂˣ) : ℂ) • p (π (diagT k (Fin n) t) v) :=
    fun t v => UnramFixed.jacB_apply π t _
  let E : Submodule ℂ (Jacquet π (unipB k (Fin n))) :=
    ⨅ (i : Fin n) (u : Uo k), Module.End.eigenspace (jacB π (Pi.mulSingle i (u : kˣ))) (((φ (eT k n i u))⁻¹ : ℂˣ) : ℂ)
  have hE : ∀ y, y ∈ E ↔ ∀ (i : Fin n) (u : Uo k),
      jacB π (Pi.mulSingle i (u : kˣ)) y = (((φ (eT k n i u))⁻¹ : ℂˣ) : ℂ) • y := fun y => by
    simp only [E, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hEs : ∀ t, ∀ y ∈ E, jacB π t y ∈ E := fun t y hy => (hE _).2 fun i u => by
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, (hE _).1 hy, map_smul]
  have hpE : ∀ v ∈ invPart π c φ, p v ∈ E := fun v hv => (hE _).2 fun i u => by
    have hO : (Pi.mulSingle i (u : kˣ) : Fin n → kˣ) ∈ torusO k (Fin n) := fun j => by
      by_cases h : j = i
      · subst h
        rw [Pi.mulSingle_eq_same]; exact u.2
      · simp [Pi.mulSingle_eq_of_ne h]
    rw [hp, UnramFixed.deltaHalf_torusO k hO, inv_one, Units.val_one, one_smul, ← map_smul]
    exact congrArg p ((heig hv).2.2 (eT k n i u))
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hl : HasFiniteLength (jacB π) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((H.loc.bz k).2.1 _ _ _ (points (Fin n)) _ π hπ (hasFiniteLength_of_isIrreducible hirr))
  haveI := GlobalTheory.TorusEigenform.secondCountableTopology_units k
  obtain ⟨μ, hμs, hμ, l, hl0, hle⟩ := OrdB.exists_form (isSmooth_jacB hπ) hl fun h => hx0 (hinj x hx h)
  obtain ⟨ψ, hψ, rfl⟩ : ∃ ψ : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ torusChar ψ = μ := by
    refine ⟨fun i => μ.comp (MonoidHom.mulSingle (fun _ => kˣ) i),
      fun i => hμs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), MonoidHom.ext fun t => ?_⟩
    rw [torusChar_apply]
    conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
    rfl
  have hsq : IsSubquotient π (prinSeries ψ) := GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hirr _ l hl0 hle
  have hψφ : ∀ i (u : Uo k), ψ i u = (φ (eT k n i u))⁻¹ := fun i u => by
    rw [← OrdB.tc_single]
    exact Units.ext (hμ _ _ ((hE _).1 (hpE x hx) i u))
  obtain ⟨hfd, -, hmult⟩ := UpperTheory.V.AlgebraTools.jqMult H.loc.geo H.loc.bz k n V π ψ hπ hψ hsq
  have hw : ∀ w : Equiv.Perm (Fin n), (∀ i (u : Uo k), ψ (w i) u = ψ i u) → w = 1 := fun w h => by
    refine Equiv.ext fun i => by_contra fun hi => ?_
    obtain ⟨u, hu⟩ := hD _ _ hi
    exact hu (inv_injective ((hψφ _ u).symm.trans ((h i u).trans (hψφ i u))))
  have hgen : E ≤ ⨅ t, Module.End.maxGenEigenspace (jacB π t) (torusChar ψ t : ℂ) := by
    refine le_iInf (OrdB.le_gen _ E hEs _ fun χ y hy hy0 hχ => ?_)
    have h1 : (⨅ t, Module.End.maxGenEigenspace (jacB π t) (χ t : ℂ) : Submodule ℂ _) ≠ ⊥ :=
      (Submodule.ne_bot_iff _).2 ⟨y, (Submodule.mem_iInf _).2 fun t =>
        (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by rw [OrdB.pow_eig (hχ t)]; simp⟩, hy0⟩
    have h2 := (Nat.pos_of_ne_zero fun h => h1 (Submodule.finrank_eq_zero.1 h)).trans_le (hmult χ)
    obtain ⟨⟨w, rfl⟩⟩ := (Nat.card_pos_iff.1 h2).1
    rw [hw w fun i u => ?_]
    · rfl
    have h3 := (hχ _).symm.trans ((hE _).1 hy i u)
    rw [OrdB.tc_single, ← hψφ] at h3
    exact Units.ext (smul_left_injective ℂ hy0 h3)
  have hE1 : Module.finrank ℂ E ≤ 1 := by
    refine (Submodule.finrank_mono hgen).trans ((hmult _).trans ?_)
    have key : ∀ a : {w : Equiv.Perm (Fin n) // torusChar ψ = torusChar (ψ ∘ w)}, a.1 = 1 := fun a =>
      hw _ fun i u => by
        have := DFunLike.congr_fun a.2 (Pi.mulSingle i (u : kˣ))
        rw [OrdB.tc_single, OrdB.tc_single] at this
        exact this.symm
    exact Finite.card_le_one_iff_subsingleton.2 ⟨fun a b => Subtype.ext ((key a).trans (key b).symm)⟩
  have hact : ∀ t, ∀ y ∈ E, jacB π t y = (torusChar ψ t : ℂ) • y := fun t y hy => by
    by_cases hy0 : y = 0
    · simp [hy0]
    have hy1 : (⟨y, hy⟩ : E) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
    have : Nontrivial E := nontrivial_of_ne _ _ hy1
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hy1).1 (le_antisymm hE1 Module.finrank_pos) ⟨_, hEs t y hy⟩
    have ha' : jacB π t y = a • y := (congrArg Subtype.val ha).symm
    rw [ha', OrdB.eq_of_gen ha' hy0 ((Submodule.mem_iInf _).1 (hgen hy) t)]
  obtain ⟨ω, rfl⟩ : ∃ ω : Fin n → kˣ →* ℂˣ, (fun i => ω i * absPow k (((n : ℂ) - 1) / 2)) = ψ :=
    ⟨fun i => ψ i * (absPow k (((n : ℂ) - 1) / 2))⁻¹, funext fun i => inv_mul_cancel_right _ _⟩
  have hω : ∀ i, IsSmoothChar (ω i) := fun i => by
    have := (hψ i).mul (isSmoothChar_of_isUnram (isUnram_absPow k (-(((n : ℂ) - 1) / 2))))
    rwa [absPow_neg, mul_inv_cancel_right] at this
  have hinv : IsInvOn φ ω := fun i u => by
    have := hψφ i u
    rw [MonoidHom.mul_apply, isUnram_absPow k _ _ u.2, mul_one] at this
    rw [this, inv_inv]
  refine ⟨ω, hω, hinv, (psIrr H k n ω hω fun i j hij => ?_).2 V π hirr hsq, le_antisymm ?_ ?_, fun v hv j hj => ?_⟩
  · obtain ⟨u, hu⟩ := hD i j hij
    rw [hinv, hinv] at hu
    refine ⟨fun h => hu (by rw [h]), fun h => hu ?_⟩
    rw [h, MonoidHom.mul_apply, isUnram_absPow k _ _ u.2, mul_one]
  · refine le_trans (LinearMap.finrank_le_finrank_of_injective (f := p.restrict hpE) ?_) hE1
    exact (injective_iff_map_eq_zero _).2 fun v h => Subtype.ext (hinj v v.2 (congrArg Subtype.val h))
  · haveI : FiniteDimensional ℂ (invPart π c φ) :=
      Submodule.finiteDimensional_of_le (heig.trans (OrdB.eig_le _ π c φ hφ))
    exact Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.1 h)
  · rw [← sub_eq_zero]
    refine hinj _ (sub_mem (OrdB.inv_stab _ π c φ hφ (al_mem k n j) hv) (Submodule.smul_mem _ _ hv)) ?_
    have h1 := propCp _ (glIwa k n) ℂ V π _ (al_mem k n j) v (heig hv).1
    rw [hker, hidx j hj] at h1
    have h2 : p _ = 0 := (Submodule.Quotient.mk_eq_zero _).2 h1
    have h3 := (hp (fun i => unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) v).symm.trans (hact _ _ (hpE v hv))
    rw [← Units.smul_def, inv_smul_eq_iff, Units.smul_def, smul_smul] at h3
    rw [map_sub, map_smul, sub_eq_zero] at h2 ⊢
    rw [h2, ← OrdB.num ω hj, mul_smul, ← h3]
    rfl
