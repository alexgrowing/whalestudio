import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorVectorEq
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsAverage

noncomputable section

open NumberField Matrix Finset
open GlobalTheory.CuspRep
open PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.GSp4Splitting

section Avg

variable {K M : Type*} [Group K] [AddCommGroup M] [Module ℂ M]

private def av (ρ : K →* Module.End ℂ M) (S : Subgroup K) (m : M) : M :=
  ((S.index : ℂ)⁻¹) • ∑ᶠ q : K ⧸ S, ρ q.out m

private theorem exists_avg [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] (ρ : K →* Module.End ℂ M)
    (hs : ∀ m, IsOpen {k | ρ k m = m}) :
    ∃ P : M →ₗ[ℂ] M, (∀ m k, ρ k (P m) = P m) ∧ (∀ m, (∀ k, ρ k m = m) → P m = m) ∧
      ∀ T : M →ₗ[ℂ] M, (∀ k m, T (ρ k m) = ρ k (T m)) → ∀ m, T (P m) = P (T m) :=
  _root_.UpperTheory.Reformulated.B.ExistsAverage.exists_avg ρ hs

end Avg

section Core

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

private theorem fin_op (π : CuspSub E n) (g k : GL (Fin n) (Af E)) (x : π.V) :
    π.finPart g (π.op (.fin k) x) = π.finPart (g * k) x :=
  Subtype.ext (by
    show finRep E n g (finRep E n k x.1) = finRep E n (g * k) x.1
    rw [map_mul, Module.End.mul_apply])

private theorem lie_fin (π : CuspSub E n) (X : Lie E n) (g : GL (Fin n) (Af E)) (x : π.V) :
    π.op (.lie X) (π.finPart g x) = π.finPart g (π.op (.lie X) x) :=
  Subtype.ext (LinearMap.congr_fun (lie_rt_fin X g) x.1)

private theorem cpt_fin (π : CuspSub E n) (c : Kinf E n) (g : GL (Fin n) (Af E)) (x : π.V) :
    π.op (.cpt c) (π.finPart g x) = π.finPart g (π.op (.cpt c) x) :=
  Subtype.ext (by
    have h := congrArg (rt E n) (infGL_comm (Unitary.toUnits c) g)
    rw [map_mul, map_mul] at h
    exact LinearMap.congr_fun h x.1)

private theorem eop_fin (π : CuspSub E n) (τ : E →+* ℂ) (i j : Fin n) (g : GL (Fin n) (Af E)) (x : π.V) :
    PositivityTheory.S2.Clozel.EopV π τ i j (π.finPart g x) = π.finPart g (PositivityTheory.S2.Clozel.EopV π τ i j x) := by
  simp only [PositivityTheory.S2.Clozel.EopV, LinearMap.smul_apply, LinearMap.sub_apply, lie_fin, map_smul, map_sub]

private theorem core (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (hKc : IsCompact (K : Set (GL (Fin n) (Af E))))
    (v0 ψ : π.V) (hv0 : v0 ≠ 0) (hfix : ∀ k ∈ K, π.finPart k v0 = v0) (hψ : ψ ≠ 0) :
    ∃ v : π.V, v ≠ 0 ∧ (∀ k ∈ K, π.finPart k v = v) ∧ ∀ (T : Module.End ℂ π.V) (c : ℂ),
      (∀ g x, T (π.finPart g x) = π.finPart g (T x)) → T ψ = c • ψ → T v = c • v := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  let ρ : K →* Module.End ℂ π.V := MonoidHom.comp π.finPart K.subtype
  have hρ : ∀ (k : K) m, ρ k m = π.finPart k.1 m := fun _ _ => rfl
  have hs : ∀ m, IsOpen {k : K | ρ k m = m} := fun m => by
    have h1 := (π.cusp m.1 m.2).1.level
    convert h1.preimage continuous_subtype_val using 1
    ext k
    exact Subtype.ext_iff
  obtain ⟨P, hPinv, hPfix, hPT⟩ := exists_avg ρ hs
  have hcomm : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.finPart g x) = π.finPart g (T x)) →
      ∀ m, T (P m) = P (T m) := fun T hT => hPT T fun k m => hT k.1 m
  let W0 : Submodule ℂ π.V := ⨅ g, LinearMap.ker (P ∘ₗ π.finPart g)
  have mem : ∀ x, x ∈ W0 ↔ ∀ g, P (π.finPart g x) = 0 := fun x => by
    simp [W0, Submodule.mem_iInf]
  have stable : IsStable (W0.map π.V.subtype) := by
    rintro o _ ⟨x, hx, rfl⟩
    refine ⟨π.op o x, ?_, rfl⟩
    have hx' := (mem x).1 hx
    refine (mem _).2 fun g => ?_
    cases o with
    | fin k => rw [fin_op]; exact hx' _
    | cpt c => rw [← cpt_fin, ← hcomm _ (fun g x => cpt_fin π c g x), hx', map_zero]
    | lie X => rw [← lie_fin, ← hcomm _ (fun g x => lie_fin π X g x), hx', map_zero]
  rcases π.irred _ (Submodule.map_subtype_le _ _) stable with h | h
  · have hn : ψ ∉ W0 := fun hm => by
      have h1 : ψ.1 ∈ W0.map π.V.subtype := ⟨ψ, hm, rfl⟩
      rw [h, Submodule.mem_bot] at h1
      exact hψ (Subtype.ext h1)
    rw [mem] at hn
    push_neg at hn
    obtain ⟨g, hg⟩ := hn
    refine ⟨P (π.finPart g ψ), hg, fun k hk => hPinv _ ⟨k, hk⟩, fun T c hT hc => ?_⟩
    rw [hcomm T hT, hT, hc, map_smul, map_smul]
  · exfalso
    have h1 : v0.1 ∈ W0.map π.V.subtype := by
      rw [h]
      exact v0.2
    obtain ⟨y, hy, e⟩ := h1
    have hy0 : y = v0 := Subtype.ext e
    subst hy0
    have h2 := (mem y).1 hy 1
    rw [map_one, Module.End.one_apply, hPfix y fun k => hfix k.1 k.2] at h2
    exact hv0 h2

end Core

theorem rlLow : HeckeMem → LowType → RlLow := by
  intro _ hL
  unfold RlLow ForRl
  intro E _ _ _ n hn π _ K _ hKc _ _ _ μf _ D hreg hnt w lam hanti hch
  obtain ⟨ν, ψ, hψ, hψ0, hk, hc⟩ := hL E n hn π hreg w lam hanti hch
  obtain ⟨u0, hu0⟩ := exists_ne (0 : D.U)
  have hv0 : D.i u0 ≠ 0 := fun e => hu0 (D.inj (by rw [e, map_zero]))
  have hfix0 : ∀ k ∈ K, π.finPart k (D.i u0) = D.i u0 := fun k hk' =>
    Subtype.ext ((D.rng (D.i u0)).1 ⟨u0, rfl⟩ k hk')
  let ψ' : π.V := ⟨ψ, hψ⟩
  have hψ' : ψ' ≠ 0 := fun e => hψ0 (congrArg Subtype.val e)
  obtain ⟨v, hv, hfix, hT⟩ := core π K hKc (D.i u0) ψ' hv0 hfix0 hψ'
  obtain ⟨u, hu⟩ := (D.rng v).2 fun k hk' => congrArg Subtype.val (hfix k hk')
  have hune : u ≠ 0 := fun e => hv (by rw [← hu, e, map_zero])
  let T : Fin n → Fin n → Module.End ℂ π.V := fun a b =>
    PositivityTheory.S2.Clozel.EopV π w.embedding a b - PositivityTheory.S2.Clozel.EopV π (ComplexEmbedding.conjugate w.embedding) b a
  have hTval : ∀ a b (x : π.V), (T a b x).1 = eopW w true a b x.1 - eopW w false b a x.1 := fun a b x => by
    simp [T, eopW, GlobalTheory.CompanionTheory.ClozelPurity.EopV_val]
  have hTc : ∀ a b g (x : π.V), T a b (π.finPart g x) = π.finPart g (T a b x) := fun a b g x => by
    simp only [T, LinearMap.sub_apply, eop_fin, map_sub]
  have hTu : ∀ a b, D.i (kF (D.E1 w) (D.E2 w) a b u) = T a b v := fun a b => Subtype.ext (by
    rw [hTval, ← hu]
    simp only [kF, LinearMap.add_apply, map_add, Submodule.coe_add, D.hE1, D.hE2]
    abel)
  have hmem : u ∈ hwSp (D.E1 w) (D.E2 w) ν := by
    refine ⟨fun a => D.inj ?_, fun a b hab he => D.inj ?_⟩
    · have h1 : T a a ψ' = (ν a : ℂ) • ψ' := Subtype.ext (by
        rw [hTval]
        exact hk.1 a)
      rw [hTu, hT _ _ (hTc a a) h1, map_smul, hu]
    · have h1 : T a b ψ' = (0 : ℂ) • ψ' := Subtype.ext (by
        rw [hTval, zero_smul]
        exact hk.2 a b hab he)
      rw [hTu, hT _ _ (hTc a b) h1, zero_smul, map_zero]
  exact ⟨ν, fun e => hune (by
    have h1 := hmem
    rw [e, Submodule.mem_bot] at h1
    exact h1), hc⟩

end UpperTheory.V.Z.GSp4Splitting
