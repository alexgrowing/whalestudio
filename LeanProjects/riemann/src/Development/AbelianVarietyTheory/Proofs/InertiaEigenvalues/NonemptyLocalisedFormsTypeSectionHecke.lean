import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionToPointEigenspaces
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.PendOf.SecProof

open GlobalTheory.EtaJoin.TypeTieProof Formalism.L2.NG Formalism.AUTREP ReciprocityTheory.Aut

def ioC {D : D7} (i : D.nd.Loc) : FractionRing (D.nd.O i) →+* ℂ := (D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)

theorem finrank_iSup_le_sum' {R V ι : Type} [Field R] [AddCommGroup V] [Module R V] [FiniteDimensional R V]
    [Fintype ι] (S : ι → Submodule R V) :
    finrank R (⨆ i, S i : Submodule R V) ≤ ∑ i, finrank R (S i) := by
  classical
  have key : ∀ s : Finset ι, finrank R (⨆ i ∈ s, S i : Submodule R V) ≤ ∑ i ∈ s, finrank R (S i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.iSup_insert, Finset.sum_insert ha]
      exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)
  have hu : (⨆ i ∈ (Finset.univ : Finset ι), S i) = ⨆ i, S i := iSup_congr fun i => iSup_pos (Finset.mem_univ i)
  rw [← hu]
  exact key Finset.univ

theorem exists_ext_dual {D : D7} (i : D.nd.Loc)
    (φ : Module.Dual (FractionRing (D.nd.O i)) (TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i))) :
    ∃ Ψ : D.what₂.Mt (D.nd.mu i) (D.nd.j i) →ₗ[ℂ] ℂ,
      ∀ y, Ψ (D.what₂.jMt _ _ y) = ioC i (φ (D.nd.prMt i y)) := by
  have hι : ∀ a, ioC i (D.nd.embK i a) = D.what₂.embLL a := D.naut.iota_LL i
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.nd.mu i) (D.nd.j i))
  have hb := D.what₂.jMt_basis (D.nd.mu i) (D.nd.j i) b
  let f0 : D.what₂.MtL (D.nd.mu i) (D.nd.j i) →ₛₗ[D.what₂.embLL] ℂ :=
    { toFun := fun z => ioC i (φ (D.nd.prMt i z))
      map_add' := fun a c => by simp only [map_add]
      map_smul' := fun a z => by
        show ioC i (φ (D.nd.prMt i (a • z))) = D.what₂.embLL a • ioC i (φ (D.nd.prMt i z))
        rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, map_mul, hι, smul_eq_mul] }
  obtain ⟨Ψ, hΨ⟩ := exists_ext_semilin D.what₂.embLL (D.what₂.jMt _ _) b hb.1 hb.2 f0
  exact ⟨Ψ, hΨ⟩

theorem typeV_le_ker {D : D7} {M : MtFam D} (i : D.nd.Loc) (HT : HeckeTied D M) (HR : HeckeRational D M)
    (AV : AVTied D M) (HS : GlobalTheory.EtaJoin.HeckeScalar M i) (x0 : D.nd.X i)
    (φ : Module.Dual (FractionRing (D.nd.O i)) (TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i)))
    (hφ0 : ∀ x, x ≠ x0 → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, φ u = 0)
    (Ψ : D.what₂.Mt (D.nd.mu i) (D.nd.j i) →ₗ[ℂ] ℂ)
    (hΨ : ∀ y, Ψ (D.what₂.jMt _ _ y) = ioC i (φ (D.nd.prMt i y)))
    (P : D.naut.AV i) (hP : D.naut.ptV i P ≠ some x0) : D.naut.typeV i P ≤ LinearMap.ker Ψ := by
  classical
  let ι := ioC (D := D) i
  have hφe := dual_eig (D.nd.T i) (D.nd.act i) (Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i) x0 φ hφ0
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.nd.mu i) (D.nd.j i))
  have hb := D.what₂.jMt_basis (D.nd.mu i) (D.nd.j i) b
  let bC : Module.Basis _ ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i)) := Module.Basis.mk hb.1 hb.2.ge
  have hbC : ∀ q, bC q = D.what₂.jMt _ _ (b q) := fun q => by simp [bC]
  intro z hz
  rw [LinearMap.mem_ker]
  by_contra hz0
  apply hP
  refine (AV.ptV i P x0).2 ?_
  intro w k s ϖ hw hc hu hk1 hk2 y' hy'
  obtain ⟨c, hcP⟩ := HS P w k s ϖ hw hc hu hk1 hk2
  choose x' hx' using HR i w k s ϖ hw hc hu hk1 hk2
  let Tt : Module.End ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i)) :=
    bC.constr ℂ (fun q => D.what₂.jMt _ _ (x' (b q)))
  have hTb : ∀ q, Tt (bC q) = D.what₂.jMt _ _ (x' (b q)) := fun q => by
    simp only [Tt, Module.Basis.constr_basis]
  have t0 : tN (M.loc i).J s ϖ k (0 : GAf D.host.E D.R.nV → (M.loc i).wt.W) = 0 := by
    have e := tN_lin HT i hw s hc ϖ hu k 1 0 0
    simp only [smul_zero, add_zero, one_smul] at e
    simpa using e
  let tl : (GAf D.host.E D.R.nV → (M.loc i).wt.W) →ₗ[ℂ] (GAf D.host.E D.R.nV → (M.loc i).wt.W) :=
    { toFun := tN (M.loc i).J s ϖ k
      map_add' := fun f f' => by simpa using tN_lin HT i hw s hc ϖ hu k 1 f f'
      map_smul' := fun a f => by simpa [t0] using tN_lin HT i hw s hc ϖ hu k a f 0 }
  have hreal : (M.loc i).real ∘ₗ Tt = tl ∘ₗ (M.loc i).real := bC.ext fun q => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hTb, hbC]
    exact hx' (b q)
  have hΨT : Ψ ∘ₗ Tt = ι (algebraMap _ (FractionRing (D.nd.O i)) ((D.nd.hT i w k : D.nd.X i → D.nd.O i) x0)) • Ψ :=
    bC.ext fun q => by
      rw [LinearMap.comp_apply, hTb, LinearMap.smul_apply, hbC, hΨ, hΨ]
      show ι (φ (D.nd.prMt i (x' (b q)))) = _ • ι (φ (D.nd.prMt i (b q)))
      rw [HT.hT i w k s ϖ hw hc hu hk1 hk2 (b q) (x' (b q)) (hx' (b q)), hφe, map_mul, smul_eq_mul]
  have hTz : Tt z = c • z := (M.loc i).real_inj (by
    have e := LinearMap.congr_fun hreal z
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at e
    rw [e, map_smul]
    exact hcP z hz)
  have hcz : c = ι (algebraMap _ (FractionRing (D.nd.O i)) ((D.nd.hT i w k : D.nd.X i → D.nd.O i) x0)) := by
    have e := LinearMap.congr_fun hΨT z
    rw [LinearMap.comp_apply, LinearMap.smul_apply, hTz, map_smul, smul_eq_mul, smul_eq_mul] at e
    exact mul_right_cancel₀ hz0 e
  rw [hcP y' hy', hcz]
  rfl

theorem typeV_le_typeSum (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) :
    D.naut.typeV i P ≤ typeSum D i (D.naut.ptV i P) :=
  le_biSup (fun P => D.naut.typeV i P) (show P ∈ {P | D.naut.ptV i P = D.naut.ptV i P} from rfl)

end GlobalTheory.PendOf.SecProof

namespace GlobalTheory.PendOf.SecProof

open GlobalTheory.EtaJoin.TypeTieProof Formalism.L2.NG Formalism.AUTREP ReciprocityTheory.Aut

set_option maxHeartbeats 1600000 in

theorem main : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc), HeckeTied D M → HeckeRational D M → AVTied D M →
    GlobalTheory.EtaJoin.SplitUnif D → GlobalTheory.EtaJoin.HeckeScalar M i → Nonempty (Sec D i) := by
  intro D M i HT HR AV _ HS
  classical
  let E := heckeEig (D.nd.T i) (D.nd.act i)
  have hint : DirectSum.IsInternal E :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
      ⟨heckeEig_iSupIndep _ _ (D.nd.T_sep i), Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i⟩
  let v := fun x => Module.Free.chooseBasis (FractionRing (D.nd.O i)) (E x)
  let bW := hint.collectedBasis v
  let ι := ioC (D := D) i

  let πh : TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i) →+
      ((Σ x, Module.Free.ChooseBasisIndex (FractionRing (D.nd.O i)) (E x)) → ℂ) :=
    { toFun := fun u k => ι (bW.repr u k)
      map_zero' := by funext k; simp
      map_add' := fun u u' => by funext k; simp }
  have hπ : ∀ u k, πh u k = ι (bW.repr u k) := fun _ _ => rfl
  have hπs : ∀ (c : FractionRing (D.nd.O i)) u, πh (c • u) = ι c • πh u := fun c u => by
    funext k
    simp only [hπ, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply]
  have hext : ∀ k : (Σ x, Module.Free.ChooseBasisIndex (FractionRing (D.nd.O i)) (E x)),
      ∃ Ψ : D.what₂.Mt (D.nd.mu i) (D.nd.j i) →ₗ[ℂ] ℂ,
        ∀ y, Ψ (D.what₂.jMt _ _ y) = ioC i (bW.coord k (D.nd.prMt i y)) := fun k => exists_ext_dual i _
  choose Ψ hΨ using hext
  let p : D.what₂.Mt (D.nd.mu i) (D.nd.j i) →ₗ[ℂ]
      ((Σ x, Module.Free.ChooseBasisIndex (FractionRing (D.nd.O i)) (E x)) → ℂ) := LinearMap.pi Ψ
  have hpj : ∀ y, p (D.what₂.jMt _ _ y) = πh (D.nd.prMt i y) := fun y => by
    funext k
    simp only [p, LinearMap.pi_apply, hΨ, hπ, Module.Basis.coord_apply]
    rfl

  have hkey : ∀ P z, z ∈ D.naut.typeV i P → ∀ k : (Σ x, Module.Free.ChooseBasisIndex (FractionRing (D.nd.O i)) (E x)),
      D.naut.ptV i P ≠ some k.1 → p z k = 0 := by
    intro P z hz k hk
    have h0 : ∀ x, x ≠ k.1 → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, bW.coord k u = 0 := by
      intro x hx u hu
      rw [Module.Basis.coord_apply]
      exact hint.collectedBasis_repr_of_mem_ne v hx hu
    exact typeV_le_ker i HT HR AV HS k.1 (bW.coord k) h0 (Ψ k) (hΨ k) P hk hz
  have hsum : ∀ (o : Option (D.nd.X i)) k, o ≠ some (Sigma.fst k) →
      typeSum D i o ≤ LinearMap.ker ((LinearMap.proj k) ∘ₗ p) := by
    intro o k hok
    refine iSup₂_le fun P hP z hz => ?_
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.proj_apply]
    exact hkey P z hz k (by rw [show D.naut.ptV i P = o from hP]; exact hok)
  have hnone : ∀ z ∈ typeSum D i none, p z = 0 := fun z hz => by
    funext k
    have := hsum none k (by simp) hz
    rwa [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.proj_apply] at this

  let G : Submodule ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i)) := ⨆ x, typeSum D i (some x)
  have hGtop : G ⊔ typeSum D i none = ⊤ := by
    rw [eq_top_iff, ← D.naut.typeV_top i]
    refine iSup_le fun P => ?_
    rcases h : D.naut.ptV i P with _ | x
    · exact le_sup_of_le_right (h ▸ typeV_le_typeSum D i P)
    · exact le_sup_of_le_left (le_iSup_of_le x (h ▸ typeV_le_typeSum D i P))

  have hπr : ∀ u, πh u ∈ LinearMap.range p := by
    intro u
    have hu : u ∈ Submodule.span (FractionRing (D.nd.O i)) (Set.range (D.nd.prMt i)) := by
      rw [D.nd.prMt_span i]; exact Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      exact ⟨_, hpj y⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add a c _ _ ha hc => rw [map_add]; exact add_mem ha hc
    | smul c a _ ha => rw [hπs]; exact Submodule.smul_mem _ _ ha
  have hrange : LinearMap.range p = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℂ _).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have : πh (bW k) = Pi.basisFun ℂ _ k := by
      funext k'
      rw [hπ, Module.Basis.repr_self, Pi.basisFun_apply]
      by_cases hk : k' = k
      · subst hk; simp
      · simp [Finsupp.single_apply, Pi.single_apply, hk, Ne.symm hk]
    rw [← this]
    exact hπr _
  let q := p ∘ₗ G.subtype
  have hqs : Function.Surjective q := by
    intro f
    obtain ⟨z, rfl⟩ := LinearMap.range_eq_top.1 hrange f
    have hz : z ∈ G ⊔ typeSum D i none := by rw [hGtop]; exact Submodule.mem_top
    obtain ⟨a, ha, n, hn, rfl⟩ := Submodule.mem_sup.1 hz
    exact ⟨⟨a, ha⟩, by simp [q, map_add, hnone n hn]⟩
  have hdim : finrank ℂ G ≤ Fintype.card (Σ x, Module.Free.ChooseBasisIndex (FractionRing (D.nd.O i)) (E x)) := by
    refine (finrank_iSup_le_sum' _).trans (le_of_eq ?_)
    rw [Fintype.card_sigma]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 := D.naut.eig_dim i x
    rw [NData.mult, heckeMult] at h1
    rw [← Module.finrank_eq_card_chooseBasisIndex]
    exact h1.symm
  have hfr : finrank ℂ G = finrank ℂ ((Σ x, Module.Free.ChooseBasisIndex (FractionRing (D.nd.O i)) (E x)) → ℂ) := by
    refine le_antisymm ?_ ?_
    · rw [Module.finrank_fintype_fun_eq_card]; exact hdim
    · have := LinearMap.finrank_range_le q
      rwa [LinearMap.range_eq_top.2 hqs, finrank_top] at this
  have hqi : Function.Injective q := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).2 hqs
  have hkerG : ∀ z, p z = 0 → z ∈ typeSum D i none := by
    intro z hz
    have hz' : z ∈ G ⊔ typeSum D i none := by rw [hGtop]; exact Submodule.mem_top
    obtain ⟨a, ha, n, hn, rfl⟩ := Submodule.mem_sup.1 hz'
    have hpa : q ⟨a, ha⟩ = q 0 := by
      rw [map_zero]
      show p a = 0
      rw [map_add, hnone n hn, add_zero] at hz
      exact hz
    have := congrArg Subtype.val (hqi hpa)
    simp only [Submodule.coe_zero] at this
    rw [this, zero_add]; exact hn
  let e := LinearEquiv.ofBijective q ⟨hqi, hqs⟩
  have hpe : ∀ f, p (e.symm f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) = f := fun f => e.apply_symm_apply f
  let Φ : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i) →+ D.what₂.Mt (D.nd.mu i) (D.nd.j i) :=
    (G.subtype ∘ₗ e.symm.toLinearMap).toAddMonoidHom.comp πh
  have hΦ : ∀ u, Φ u = (e.symm (πh u) : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) := fun _ => rfl
  refine ⟨⟨Φ, ?_, ?_, ?_, ?_⟩⟩
  ·
    refine (injective_iff_map_eq_zero Φ).2 fun u hu => ?_
    rw [hΦ] at hu
    have h1 : e.symm (πh u) = 0 := Subtype.ext hu
    have h2 : πh u = 0 := by simpa using congrArg e h1
    refine bW.repr.injective (Finsupp.ext fun k => ?_)
    have h3 := congrFun h2 k
    rw [hπ] at h3
    simpa using (map_eq_zero_iff ι ι.injective).1 h3
  ·
    intro c u
    rw [hΦ, hΦ, hπs, map_smul, Submodule.coe_smul]
    rfl
  ·
    intro x u hu
    rw [hΦ]
    set g := e.symm (πh u) with hg
    have hpg : p (g : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) = πh u := hpe _
    have hGle : G ≤ typeSum D i (some x) ⊔ ⨆ (x') (_ : x' ≠ x), typeSum D i (some x') := by
      refine iSup_le fun x' => ?_
      by_cases hx : x' = x
      · subst hx; exact le_sup_left
      · exact le_sup_of_le_right (le_biSup (fun x' => typeSum D i (some x')) hx)
    obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.1 (hGle g.2)
    have hcG : c ∈ G := by
      refine (iSup₂_le fun x' _ => le_iSup (fun x => typeSum D i (some x)) x') hc
    have hpc : p c = 0 := by
      funext k
      by_cases hk : k.1 = x
      · have hle : (⨆ (x') (_ : x' ≠ x), typeSum D i (some x')) ≤ LinearMap.ker ((LinearMap.proj k) ∘ₗ p) :=
          iSup₂_le fun x' hx' => hsum (some x') k (by rw [hk]; simpa using hx')
        have := hle hc
        rwa [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.proj_apply] at this
      · have h1 := hsum (some x) k (by simpa using Ne.symm hk) ha
        rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.proj_apply] at h1
        have h2 : p (g : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) k = 0 := by
          rw [hpg, hπ, show bW.repr u k = 0 from hint.collectedBasis_repr_of_mem_ne v (Ne.symm hk) hu, map_zero]
        rw [← hac, map_add, Pi.add_apply, h1, zero_add] at h2
        simpa using h2
    have hc0 : c = 0 := by
      have := congrArg Subtype.val (hqi (a₁ := ⟨c, hcG⟩) (a₂ := 0) (by
        rw [map_zero]; exact hpc))
      simpa using this
    rw [← hac, hc0, add_zero]
    exact ha
  ·
    intro y
    refine hkerG _ ?_
    rw [map_sub, hΦ, hpe, hpj, sub_self]

end GlobalTheory.PendOf.SecProof
