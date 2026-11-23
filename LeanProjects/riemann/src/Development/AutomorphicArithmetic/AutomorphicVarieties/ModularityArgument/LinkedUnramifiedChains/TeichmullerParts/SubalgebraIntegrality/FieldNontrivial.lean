import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSemi

open Polynomial TensorProduct

namespace UpperTheory.V.Z.J.D

section Nil

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

private theorem ge_add {f g : Module.End K V} (h : Commute f g) {μ ν : K} {v : V} (h1 : v ∈ f.maxGenEigenspace μ)
    (h2 : v ∈ g.maxGenEigenspace ν) : v ∈ (f + g).maxGenEigenspace (μ + ν) := by
  simpa using Module.End.genEigenspace_inf_le_add f g μ ν ⊤ ⊤ h ⟨h1, h2⟩

private theorem ge_left {a f : Module.End K V} (h : Commute a f) {μ : K} {v : V} (h1 : v ∈ f.maxGenEigenspace μ) :
    v ∈ (a * (f - μ • 1)).maxGenEigenspace 0 := by
  rw [Module.End.mem_maxGenEigenspace] at h1 ⊢
  obtain ⟨k, hk⟩ := h1
  have hc : Commute a (f - μ • 1) := h.sub_right ((Commute.one_right a).smul_right μ)
  exact ⟨k, by rw [zero_smul, sub_zero, hc.mul_pow, Module.End.mul_apply, hk, map_zero]⟩

private theorem ge_scal (c : K) (v : V) : v ∈ (c • (1 : Module.End K V)).maxGenEigenspace c := by
  rw [Module.End.mem_maxGenEigenspace]
  exact ⟨1, by simp⟩

private theorem ge_mul {f g : Module.End K V} (h : Commute f g) {μ ν : K} {v : V} (h1 : v ∈ f.maxGenEigenspace μ)
    (h2 : v ∈ g.maxGenEigenspace ν) : v ∈ (f * g).maxGenEigenspace (μ * ν) := by
  have s : ∀ (c : K) (p : Module.End K V), Commute (c • (1 : Module.End K V)) p := fun c p =>
    (Commute.one_left p).smul_left c
  have a1 := ge_left h h2
  have a2 := ge_left (s ν f) h1
  have fg : Commute f (g - ν • 1) := h.sub_right (s ν f).symm
  have c1 : Commute (f * (g - ν • 1)) (ν • 1 * (f - μ • 1)) :=
    (s ν _).symm.mul_right (((Commute.refl f).mul_left fg.symm).sub_right (s μ _).symm)
  have a3 := ge_add (s (μ * ν) _).symm (ge_add c1 a1 a2) (ge_scal (μ * ν) v)
  have e : f * (g - ν • 1) + ν • 1 * (f - μ • 1) + (μ * ν) • (1 : Module.End K V) = f * g := by
    simp only [mul_sub, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, smul_smul]
    abel
  rwa [e, zero_add, zero_add] at a3

private theorem ne_bot_of_quot {I Q : Type} [AddCommGroup Q] [Module K Q] [FiniteDimensional K V] [IsAlgClosed K]
    (f : I → Module.End K V) (hc : ∀ i j, Commute (f i) (f j)) (x : I → K) (π : V →ₗ[K] Q) (hπ : π ≠ 0)
    (h : ∀ i v, π (f i v) = x i • π v) : (⨅ i, (f i).maxGenEigenspace (x i)) ≠ ⊥ := by
  intro h0
  apply hπ
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
    (fun i j _ => hc i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i))
  rw [← LinearMap.ker_eq_top, eq_top_iff, ← htop]
  refine iSup_le fun χ v hv => ?_
  by_cases e : χ = x
  · rw [e, h0, Submodule.mem_bot] at hv
    simp [hv]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 e
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hv i)
    have p : ∀ (k : ℕ) (w : V), π (((f i - χ i • 1) ^ k) w) = (x i - χ i) ^ k • π w := by
      intro k
      induction k with
      | zero => intro w; simp
      | succ k ih =>
        intro w
        rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, map_sub, h, LinearMap.smul_apply, map_smul,
          Module.End.one_apply, ih, ← sub_smul, smul_smul, ← pow_succ']
    have q := p k v
    rw [hk, map_zero] at q
    exact (smul_eq_zero.1 q.symm).resolve_left (pow_ne_zero _ (sub_ne_zero.2 (Ne.symm hi)))

private theorem transport {C W I : Type} [Field C] [AddCommGroup W] [Module C W] (ι : K ≃+* C) (Ψ : V →+ W)
    (hs : ∀ (k : K) v, Ψ (k • v) = ι k • Ψ v) (hi : Function.Injective Ψ) (S : Submodule C W) (hS : ∀ w, w ∈ S ↔ ∃ v, Ψ v = w)
    (f : I → Module.End K V) (γ : I → Module.End C W) (h : ∀ i v, Ψ (f i v) = γ i (Ψ v)) (x : I → K) :
    Module.rank K ↥(⨅ i, (f i).maxGenEigenspace (x i)) = Module.rank C ↥(S ⊓ ⨅ i, (γ i).maxGenEigenspace (ι (x i))) := by
  have p : ∀ i (k : ℕ) (v : V), Ψ (((f i - x i • 1) ^ k) v) = ((γ i - ι (x i) • 1) ^ k) (Ψ v) := by
    intro i k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      simp only [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, map_sub, h, LinearMap.smul_apply, hs,
        Module.End.one_apply, ih]
  have q : ∀ v, v ∈ (⨅ i, (f i).maxGenEigenspace (x i)) ↔ Ψ v ∈ S ⊓ ⨅ i, (γ i).maxGenEigenspace (ι (x i)) := by
    intro v
    simp only [Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_maxGenEigenspace, ← p, map_eq_zero_iff Ψ hi, hS]
    exact ⟨fun a => ⟨⟨v, rfl⟩, a⟩, fun a => a.2⟩
  let φ : ↥(⨅ i, (f i).maxGenEigenspace (x i)) →+ ↥(S ⊓ ⨅ i, (γ i).maxGenEigenspace (ι (x i))) :=
    { toFun := fun v => ⟨Ψ v.1, (q _).1 v.2⟩
      map_zero' := Subtype.ext (map_zero Ψ)
      map_add' := fun a b => Subtype.ext (map_add Ψ a.1 b.1) }
  have hb : Function.Bijective φ := by
    refine ⟨fun a b e => Subtype.ext (hi (congrArg Subtype.val e)), fun w => ?_⟩
    obtain ⟨v, hv⟩ := (hS w.1).1 w.2.1
    exact ⟨⟨v, (q v).2 (hv ▸ w.2)⟩, Subtype.ext hv⟩
  exact rank_eq_of_equiv_equiv ι (AddEquiv.ofBijective φ hb) ι.bijective fun k v => Subtype.ext (hs k v.1)

end Nil

section Fibre

variable {A B K M : Type} [CommRing A] [CommRing B] [Field K] [Algebra A B] [Algebra B K] [Algebra A K] [IsScalarTower A B K]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

private theorem field_nontrivial (k K N : Type) [Field k] [Field K] [Algebra k K] [AddCommGroup N] [Module k N] [Nontrivial N] :
    Nontrivial (K ⊗[k] N) := by
  haveI : Module.Free k K := Module.Free.of_divisionRing k K
  haveI : Module.Free k N := Module.Free.of_divisionRing k N
  haveI : Module.Free k (K ⊗[k] N) := Module.Free.of_divisionRing k _
  rw [← Module.rank_pos_iff_of_free (R := k), rank_tensorProduct']
  exact pos_iff_ne_zero.2 (mul_ne_zero Module.rank_pos_of_free.ne' Module.rank_pos_of_free.ne')

private theorem fibre_nontrivial [Module.Finite B M] (hann : ∀ b : B, (∀ m : M, b • m = 0) → algebraMap B K b = 0) :
    Nontrivial (K ⊗[B] M) := by
  let p : PrimeSpectrum B := ⟨RingHom.ker (algebraMap B K), RingHom.ker_isPrime _⟩
  have hp : p ∈ Module.support B M := by
    rw [Module.support_eq_zeroLocus]
    exact fun b hb => hann b (Module.mem_annihilator.1 hb)
  have h1 := (Module.mem_support_iff_nontrivial_residueField_tensorProduct p).1 hp
  let r : p.asIdeal.ResidueField →ₐ[B] K := Ideal.ResidueField.liftₐ p.asIdeal (Algebra.ofId B K) le_rfl
    (fun b hb => isUnit_iff_ne_zero.2 hb)
  letI := r.toRingHom.toAlgebra
  haveI : IsScalarTower B p.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq fun b => (r.commutes b).symm
  have h2 : Nontrivial (K ⊗[p.asIdeal.ResidueField] (p.asIdeal.ResidueField ⊗[B] M)) := field_nontrivial _ _ _
  exact (AlgebraTensorModule.cancelBaseChange B p.asIdeal.ResidueField K K M).symm.toEquiv.nontrivial

end Fibre

section Main

open UpperTheory.V.J

variable {O A B K : Type} [CommRing O] [CommRing A] [CommRing B] [Field K] [Algebra O A] [Algebra O B] [Algebra O K]
  (lam : A →ₐ[O] B) (M : Type) [AddCommGroup M] [Module B M] [Module A M] (hs : ∀ (a : A) (m : M), a • m = lam a • m)

private theorem act_add (a b : B) : actL lam M hs (a + b) = actL lam M hs a + actL lam M hs b :=
  LinearMap.ext fun m => add_smul a b m

private theorem act_mul (a b : B) : actL lam M hs (a * b) = actL lam M hs a * actL lam M hs b :=
  LinearMap.ext fun m => mul_smul a b m

private theorem act_lam (a : A) : actL lam M hs (lam a) = algebraMap A _ a :=
  LinearMap.ext fun m => (hs a m).symm

private theorem act_comm [Algebra A K] (a b : B) :
    Commute ((actL lam M hs a).baseChange K) ((actL lam M hs b).baseChange K) := by
  rw [Commute, SemiconjBy, ← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, ← act_mul, ← act_mul, mul_comm]

variable (y : B →ₐ[O] K) (hann : ∀ b : B, (∀ m : M, b • m = 0) → y b = 0)

include hann in
private theorem joint_ne [IsAlgClosed K] [Module.Finite A M] [Algebra A K] (hK : ∀ a, algebraMap A K a = y (lam a)) :
    (⨅ b : B, Module.End.maxGenEigenspace ((actL lam M hs b).baseChange K) (y b)) ≠ ⊥ := by
  letI : Algebra A B := lam.toRingHom.toAlgebra
  letI : Algebra B K := y.toRingHom.toAlgebra
  haveI : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq hK
  haveI : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul fun a m => (hs a m).symm
  haveI : Module.Finite B M := Module.Finite.of_restrictScalars_finite A B M
  haveI := fibre_nontrivial (B := B) (K := K) (M := M) hann
  refine ne_bot_of_quot _ (act_comm lam M hs) _ (TensorProduct.mapOfCompatibleSMul B A K K M) ?_ ?_
  · intro h0
    obtain ⟨q, hq⟩ := exists_ne (0 : K ⊗[B] M)
    obtain ⟨v, rfl⟩ := TensorProduct.mapOfCompatibleSMul_surjective B A K K M q
    exact hq (by rw [h0]; rfl)
  · intro b v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add, hu, hv, smul_add]
    | tmul k m =>
      rw [LinearMap.baseChange_tmul, TensorProduct.mapOfCompatibleSMul_tmul, TensorProduct.mapOfCompatibleSMul_tmul]
      exact (TensorProduct.tmul_smul b k m).trans (algebraMap_smul K b _).symm

include hann in
private theorem joint_gen {I : Type} (g : I → B)
    (hg : ∀ b, actL lam M hs b ∈ Algebra.adjoin A (Set.range fun i => actL lam M hs (g i)))
    [Algebra A K] (hK : ∀ a, algebraMap A K a = y (lam a)) :
    (⨅ b : B, Module.End.maxGenEigenspace ((actL lam M hs b).baseChange K) (y b)) =
      ⨅ i, Module.End.maxGenEigenspace ((actL lam M hs (g i)).baseChange K) (y (g i)) := by
  refine le_antisymm (le_iInf fun i => iInf_le _ (g i)) fun v hv => (Submodule.mem_iInf _).2 fun b => ?_
  have key : ∀ φ ∈ Algebra.adjoin A (Set.range fun i => actL lam M hs (g i)),
      ∃ b, actL lam M hs b = φ ∧ v ∈ Module.End.maxGenEigenspace ((actL lam M hs b).baseChange K) (y b) := by
    intro φ hφ
    induction hφ using Algebra.adjoin_induction with
    | mem φ h =>
      obtain ⟨i, rfl⟩ := h
      exact ⟨g i, rfl, (Submodule.mem_iInf _).1 hv i⟩
    | algebraMap a =>
      refine ⟨lam a, act_lam lam M hs a, ?_⟩
      rw [act_lam, Algebra.algebraMap_eq_smul_one, LinearMap.baseChange_smul, LinearMap.baseChange_one, ← hK,
        ← algebraMap_smul K a]
      exact ge_scal _ v
    | add _ _ _ _ h1 h2 =>
      obtain ⟨b1, rfl, m1⟩ := h1
      obtain ⟨b2, rfl, m2⟩ := h2
      refine ⟨b1 + b2, act_add lam M hs b1 b2, ?_⟩
      rw [act_add, LinearMap.baseChange_add, map_add]
      exact ge_add (act_comm lam M hs b1 b2) m1 m2
    | mul _ _ _ _ h1 h2 =>
      obtain ⟨b1, rfl, m1⟩ := h1
      obtain ⟨b2, rfl, m2⟩ := h2
      refine ⟨b1 * b2, act_mul lam M hs b1 b2, ?_⟩
      rw [act_mul, LinearMap.baseChange_mul, map_mul]
      exact ge_mul (act_comm lam M hs b1 b2) m1 m2
  obtain ⟨b', e, hm⟩ := key _ (hg b)
  have e' : y b' = y b := by
    rw [← sub_eq_zero, ← map_sub]
    exact hann _ fun m => by rw [sub_smul, sub_eq_zero]; exact LinearMap.congr_fun e m
  rwa [e, e'] at hm

omit [Module B M] in
private theorem exists_semi [Algebra A K] [Module.Free A M] {C W : Type} [Field C] [AddCommGroup W] [Module C W] (ι : K ≃+* C)
    (sp : M →+ W) (hsm : ∀ (a : A) m, sp (a • m) = ι (algebraMap A K a) • sp m)
    (hind : ∀ (κ : Type) (b : Module.Basis κ A M), LinearIndependent C fun i => sp (b i)) :
    ∃ Ψ : K ⊗[A] M →+ W, (∀ k m, Ψ (k ⊗ₜ m) = ι k • sp m) ∧ (∀ (k : K) v, Ψ (k • v) = ι k • Ψ v) ∧ Function.Injective Ψ ∧
      ∀ w, w ∈ Submodule.span C (Set.range sp) ↔ ∃ v, Ψ v = w :=
  by apply _root_.UpperTheory.Reformulated.B.Ra9.exists_semi <;> assumption

include hann in
private theorem mu_eq [IsAlgClosed K] [Module.Finite A M] [Module.Free A M] {I : Type} (g : I → B)
    (hg : ∀ b, actL lam M hs b ∈ Algebra.adjoin A (Set.range fun i => actL lam M hs (g i)))
    {C W : Type} [Field C] [AddCommGroup W] [Module C W] (ι : K ≃+* C)
    (sp : M →+ W) (hsm : ∀ (a : A) m, sp (a • m) = ι (y (lam a)) • sp m)
    (hind : ∀ (κ : Type) (b : Module.Basis κ A M), LinearIndependent C fun i => sp (b i))
    (γ : I → Module.End C W) (hop : ∀ i m, sp (g i • m) = γ i (sp m)) (Z : Submodule C W)
    (hZ : Z = Submodule.span C (Set.range sp) ⊓ ⨅ i, (γ i).maxGenEigenspace (ι (y (g i)))) :
    Z ≠ ⊥ ∧ mu lam M hs y = Module.finrank C Z := by
  unfold mu
  letI : Algebra A K := (y.comp lam).toRingHom.toAlgebra
  have hK : ∀ a, algebraMap A K a = y (lam a) := fun _ => rfl
  obtain ⟨Ψ, ht, hk, hi, hr⟩ := exists_semi M ι sp hsm hind
  have hne := joint_ne lam M hs y hann hK
  rw [joint_gen lam M hs y hann g hg hK] at hne ⊢
  have tr := transport ι Ψ hk hi _ hr (fun i => (actL lam M hs (g i)).baseChange K) γ (fun i v => by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul k m => rw [LinearMap.baseChange_tmul, ht, ht, map_smul, ← hop]; rfl) fun i => y (g i)
  subst hZ
  refine ⟨fun h0 => hne ?_, congrArg Cardinal.toNat tr⟩
  rw [h0, rank_bot] at tr
  haveI := Module.Free.of_divisionRing K
    ↥(⨅ i, Module.End.maxGenEigenspace (LinearMap.baseChange K (actL lam M hs (g i))) (y (g i)))
  exact Submodule.subsingleton_iff_eq_bot.1 (Module.rank_zero_iff_of_free.1 tr)

end Main

section Hecke

open UpperTheory.V.J UpperTheory.V.Hi

private theorem mu_hecke {O A B K M₀ I C W : Type} [CommRing O] [CommRing A] [CommRing B] [Field K] [IsAlgClosed K] [Algebra O A]
    [Algebra O B] [Algebra O K] [AddCommGroup M₀] [Module A M₀] (Y Y₀ : Submodule A M₀) (hY : Y ≤ Y₀) (op : I → Module.End A M₀)
    [Fact (CommOn Y op)] [Module.Finite A Y] [Module.Free A Y] [Algebra O (heckeAlg Y op)] (j : A →ₐ[O] B)
    (f : B →ₐ[O] heckeAlg Y op) (hf : Function.Surjective f) [Module B Y] (hs : ∀ (b : A) (m : Y), b • m = j b • m)
    (hB : ∀ (b : B) (m : Y), b • m = (f b).1 m) (z : heckeAlg Y op →ₐ[O] K) (x : A →+* K)
    (hz : z.toRingHom.comp (algebraMap A _) = x) [Field C] [AddCommGroup W] [Module C W] (ι : K ≃+* C) (sp : M₀ → W)
    (hadd : ∀ f ∈ Y₀, ∀ f' ∈ Y₀, sp (f + f') = sp f + sp f') (hsm : ∀ f ∈ Y₀, ∀ b : A, sp (b • f) = ι (x b) • sp f)
    (γ : I → Module.End C W) (hop : ∀ i, ∀ f ∈ Y₀, sp (op i f) = γ i (sp f)) (Z : Submodule C W)
    (h : (∀ (κ : Type) (b : Module.Basis κ A Y), LinearIndependent C fun i => sp (b i)) ∧
      Z = Submodule.span C (sp '' Y) ⊓ ⨅ i, (γ i).maxGenEigenspace (ι (z (heckeGen Y op i)))) :
    Z ≠ ⊥ ∧ mu j Y hs (z.comp f) = Module.finrank C Z := by
  choose g hg using fun i => hf (heckeGen Y op i)
  have hact : ∀ b, actL j Y hs b = (f b).1 := fun b => LinearMap.ext (hB b)
  have hj : ∀ a, f (j a) = algebraMap A _ a := fun a => Subtype.ext ((hact _).symm.trans (act_lam j Y hs a))
  refine mu_eq j Y hs (z.comp f) (fun b hb => ?_) g (fun b => ?_) ι
    (AddMonoidHom.mk' (fun m : Y => sp m) fun m m' => hadd _ (hY m.2) _ (hY m'.2)) (fun a m => ?_) h.1 γ (fun i m => ?_) Z ?_
  · have e : f b = 0 := Subtype.ext (LinearMap.ext fun m => (hB b m).symm.trans (hb m))
    rw [AlgHom.comp_apply, e, map_zero]
  · rw [hact]
    refine Algebra.adjoin_mono ?_ (f b).2
    rintro t ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simp only [hact, hg]
    exact LinearMap.ext fun m => Subtype.ext (hi m).symm
  · rw [AlgHom.comp_apply, hj, ← hz] at *
    exact hsm _ (hY m.2) a
  · rw [hB, hg]
    exact hop i _ (hY m.2)
  · rw [h.2]
    simp only [AlgHom.comp_apply, hg]
    congr 2
    ext w
    exact ⟨fun ⟨m, hm, e⟩ => ⟨⟨m, hm⟩, e⟩, fun ⟨m, e⟩ => ⟨m.1, m.2, e⟩⟩

end Hecke

end UpperTheory.V.Z.J.D

open UpperTheory.V.Z.J.D

theorem UpperTheory.V.Z.J.D.muZ :
    LocSp → MuZ := by
  intro hL L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ hθ ι x lam d ξ c0 sp hsp K a _ B _ _ j f hf _ hs hB z hz
  haveI := ((UpperTheory.V.Hi.hiComm L Ω l n c H hA A θ hθ K).2.2.2 a).2.1
  haveI := ((UpperTheory.V.Hi.hiComm L Ω l n c H hA A θ hθ K).2.2.2 a).2.2
  exact mu_hecke (H.MK θ a K) (H.X.Ord (H.τA A) θ (H.lev K)) inf_le_left (H.op A) j f hf hs hB z x.toRingHom hz ι sp
    (hsp.add K) (hsp.smul K) (H.opC ι lam d) (hsp.op K) _ (hL L Ω l n c H hA A θ hθ ι x lam d ξ c0 sp hsp K a z hz)
