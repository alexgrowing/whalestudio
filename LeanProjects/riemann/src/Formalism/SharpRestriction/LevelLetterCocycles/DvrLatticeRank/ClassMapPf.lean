import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionFree
import Formalism.SharpRestriction.LevelLetterCocycles.MapCompZero
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrobPiNPf

noncomputable section

namespace Formalism.MainNotions.N.Ln34.ClassMapPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem classMapPf_mem_Z1DΔ (y z : W.DD T) (hy : y ∈ DelS W T) (hz : z ∈ DelS W T)
    (h : W.γD T W.gamK y - y = W.φD T z - z) : (y, z) ∈ W.wachCocyclesDelta T := by
  have hy' : ∀ δ ∈ W.DelF, W.γD T δ y = y := by simpa [DelS, sub_eq_zero] using hy
  have hz' : ∀ δ ∈ W.DelF, W.γD T δ z = z := by simpa [DelS, sub_eq_zero] using hz
  show (y, z) ∈ herrZ1Δ (W.γD T W.gamK) (W.φD T) W.DelF (W.γD T)
  rw [herrZ1Δ, Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [herrCocycles]
    simp only [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.neg_apply,
      LinearMap.id_apply]
    rw [h]
    abel
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.prodMap_apply,
      LinearMap.id_apply]
    intro δ hδ
    rw [hy' δ hδ, hz' δ hδ, sub_self]

theorem classMapPf_cocycle {y z : W.DD T} (h : (y, z) ∈ W.wachCocyclesDelta T) :
    W.γD T W.gamK y - y = W.φD T z - z := by
  have h0 : (y, z) ∈ herrZ1Δ (W.γD T W.gamK) (W.φD T) W.DelF (W.γD T) := h
  rw [herrZ1Δ, Submodule.mem_inf] at h0
  have h1 := h0.1
  rw [herrCocycles] at h1
  simp only [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.id_apply] at h1
  rwa [← sub_eq_add_neg, sub_eq_zero] at h1

theorem classMapPf_local (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n)
    (hF : FrobPiN W T π' M)
    (hγ : ∀ x ∈ PiNS W T π' M, W.γD T W.gamK x ∈ PiNS W T π' M)
    (hker : ∀ w : ↥(W.wachCocyclesDelta T), (∃ m : W.DD T, Formalism.MainNotions.DeltaInvariantLattices.DInv W T m ∧
        (w : W.DD T × W.DD T) = (W.φD T m - m, W.γD T W.gamK m - m)) → W.clK T w = 0)
    (hf : ∀ pr : ↥(W.wachCocyclesDelta T), pr.1.1 ∈ InvS W T π' Eπ h' M c → pr.1.2 ∈ PiNS W T π' M →
        W.clK T pr ∈ latticeFiniteCohomology PD T.L) :
    ClassMap W T π' Eπ h' M c := by
  have hPiDel : ∀ x ∈ PiNS W T π' M, x ∈ DelS W T := fun x hx =>
    (Submodule.mem_inf.mp (show x ∈ (Formalism.MainNotions.DeltaInvariantLattices.aN W T (π' ^ M)).restrictScalars O ⊓ DelS W T from hx)).2
  have hPiD : ∀ x ∈ PiNS W T π' M, ∀ δ ∈ W.DelF, W.γD T δ x = x := by
    intro x hx
    simpa [DelS, sub_eq_zero] using hPiDel x hx
  refine ⟨fun w hw => ?_, fun pr pr' hy hz hy' hz' hdiff => ?_, fun pr hy hz => ?_⟩
  · simp only [InvS, LamPS, Submodule.mem_inf, Submodule.mem_comap] at hw
    obtain ⟨⟨⟨_, hwD⟩, _⟩, hwP⟩ := hw
    have hb : W.γD T W.gamK w - w ∈ PiNS W T π' M := by simpa using hwP
    obtain ⟨x, ⟨hxP, hx⟩, _⟩ := hF.2 _ hb
    exact ⟨x, hxP, classMapPf_mem_Z1DΔ W T w x hwD (hPiDel x hxP) hx.symm⟩
  · have hc := classMapPf_cocycle W T pr.2
    have hc' := classMapPf_cocycle W T pr'.2
    obtain ⟨m, ⟨hmP, hm⟩, _⟩ := hF.2 _ hdiff
    have hm' : W.φD T m = (pr.1.1 - pr'.1.1) + m := by rw [← hm, sub_add_cancel]
    have hvP : pr.1.2 - pr'.1.2 ∈ PiNS W T π' M := Submodule.sub_mem _ hz hz'
    have hwP : W.γD T W.gamK m - m - (pr.1.2 - pr'.1.2) ∈ PiNS W T π' M :=
      Submodule.sub_mem _ (Submodule.sub_mem _ (hγ m hmP) hmP) hvP
    have hφw : W.φD T (W.γD T W.gamK m - m - (pr.1.2 - pr'.1.2)) -
        (W.γD T W.gamK m - m - (pr.1.2 - pr'.1.2)) = 0 := by
      have key : (W.γD T W.gamK pr.1.1 - pr.1.1 - (W.φD T pr.1.2 - pr.1.2)) -
          (W.γD T W.gamK pr'.1.1 - pr'.1.1 - (W.φD T pr'.1.2 - pr'.1.2)) = 0 := by
        rw [hc, hc']; abel
      simp only [map_sub, map_add, W.φγ_comm, hm']
      rw [← key]
      abel
    have hw0 : W.γD T W.gamK m - m - (pr.1.2 - pr'.1.2) = 0 := by
      obtain ⟨x0, _, hu0⟩ := hF.2 0 (Submodule.zero_mem _)
      have a1 := hu0 _ ⟨hwP, hφw⟩
      have a2 := hu0 0 ⟨Submodule.zero_mem _, by simp⟩
      exact a1.trans a2.symm
    have hk := hker (pr - pr') ⟨m, fun δ hδ => hPiD m hmP δ hδ, by
      refine Prod.ext ?_ ?_ <;>
        simp only [Submodule.coe_sub, Prod.fst_sub, Prod.snd_sub, hm, sub_eq_zero.mp hw0]⟩
    have hsub : W.clK T (pr - pr') = W.clK T pr - W.clK T pr' := by
      first
        | exact map_sub (W.clK T) pr pr'
        | exact (W.clK T).map_sub pr pr'
        | exact LinearMap.map_sub _ _ _
        | simp
    rw [hsub, sub_eq_zero] at hk
    exact hk
  · have h1 := hf pr hy hz
    obtain ⟨κ0, hκ0, hκeq⟩ := Submodule.mem_map.mp h1
    exact ⟨κ0.1, Submodule.mem_comap.mp hκ0, κ0.2, hκeq⟩

theorem classMapPf_φspan (S : Submodule (LetA O n) (W.DD T)) (hS : S ≤ W.N T) :
    ∀ u ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T S, ∃ k : ℕ, W.Q ^ k • u ∈ W.N T := by
  have hφN : ∀ x ∈ W.N T, ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ W.N T := by
    exact W.N_φ T
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact hφN s (hS hs)
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨k1, h1⟩ := hx
    obtain ⟨k2, h2⟩ := hy
    refine ⟨k1 + k2, ?_⟩
    rw [smul_add]
    refine (W.N T).add_mem ?_ ?_
    · rw [pow_add, mul_comm, mul_smul]; exact (W.N T).smul_mem _ h1
    · rw [pow_add, mul_smul]; exact (W.N T).smul_mem _ h2
  | smul a x _ hx =>
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, by rw [smul_comm]; exact (W.N T).smul_mem a hk⟩

theorem classMapPf_of (π' : LetA O n) (E : ZMod n → Polynomial O) (e s' h' M : ℕ) (c : ZMod n)
    (hs1 : W.s = 1) (hp2 : PD.p ≠ 2) (hs' : 1 ≤ s') (hM : 1 ≤ M)
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (hF : FrobPiN W T π' M)
    (h2a : Formalism.MainNotions.DeltaInvariantLattices.p2aK W T) (h2b : Formalism.MainNotions.DeltaInvariantLattices.p2b W T) (h7 : Formalism.MainNotions.DeltaInvariantLattices.p7 W T)
    (hres : Formalism.MainNotions.CrystallineLiftingBounds.coreResK W) :
    ClassMap W T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' M c := by
  have hγK : W.gamK = W.gam := W.gamK_eq_one hs1 hp2
  obtain ⟨_, _, ⟨wπ, hwπ⟩, _, ⟨wq, hwq⟩, _, ⟨wγ, hwγ⟩, _⟩ := hp9
  have hQ : W.Q = W.q := by
    show (W.φA ^ (W.s - 1)) W.q = W.q
    rw [hs1]
    first | rfl | simp
  have hNγ : ∀ x ∈ W.N T, W.γD T W.gam x ∈ W.N T := by
    exact fun x hx => W.N_Γ T W.gam x hx
  have hsm : ∀ (a : LetA O n) (y : W.DD T), W.γD T W.gam (a • y) = letγ (W.γ₀ W.gam) a • W.γD T W.gam y := by
    intro a y
    rw [← algebraMap_smul W.EE a y, W.γD_smul, W.γE_ext, algebraMap_smul]
  have hγπ : letγ (W.γ₀ W.gam) π' = π' * (1 + (wγ : LetA O n) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π') := by
    have h0 := hwγ
    rw [sub_eq_iff_eq_add] at h0
    rw [show letγ (W.γ₀ W.gam) π' = W.γA W.gam π' from rfl, h0]
    ring
  have hγ : ∀ x ∈ PiNS W T π' M, W.γD T W.gamK x ∈ PiNS W T π' M := by
    intro x hx
    rw [hγK]
    obtain ⟨hxa, hxD⟩ := Submodule.mem_inf.mp
      (show x ∈ (Formalism.MainNotions.DeltaInvariantLattices.aN W T (π' ^ M)).restrictScalars O ⊓ DelS W T from hx)
    have hD : W.γD T W.gam x ∈ DelS W T := by
      simp only [DelS, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
        sub_eq_zero] at hxD ⊢
      intro δ hδ
      rw [← W.γD_mul, mul_comm, W.γD_mul, hxD δ hδ]
    rw [Submodule.restrictScalars_mem] at hxa
    obtain ⟨y, hyN, rfl⟩ := Submodule.mem_map.mp hxa
    show _ ∈ (Formalism.MainNotions.DeltaInvariantLattices.aN W T (π' ^ M)).restrictScalars O ⊓ DelS W T
    refine Submodule.mem_inf.mpr ⟨?_, hD⟩
    rw [Submodule.restrictScalars_mem]
    refine Submodule.mem_map.mpr ⟨((1 : LetA O n) + (wγ : LetA O n) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π') ^ M •
      W.γD T W.gam y, (W.N T).smul_mem _ (hNγ y hyN), ?_⟩
    show π' ^ M • ((1 + (wγ : LetA O n) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π') ^ M • W.γD T W.gam y) =
      W.γD T W.gam (π' ^ M • y)
    rw [hsm, map_pow, hγπ, mul_pow, mul_smul]
  have hker : ∀ w : ↥(W.wachCocyclesDelta T), (∃ m : W.DD T, Formalism.MainNotions.DeltaInvariantLattices.DInv W T m ∧
      (w : W.DD T × W.DD T) = (W.φD T m - m, W.γD T W.gamK m - m)) → W.clK T w = 0 :=
    fun w hw => ((h2a hs1 hp2).2 w).mpr hw
  have hE : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' = ((wq⁻¹ : (LetA O n)ˣ) : LetA O n) * W.q := by
    rw [hwq, ← mul_assoc, Units.inv_mul, one_mul]
  have hf : ∀ pr : ↥(W.wachCocyclesDelta T), pr.1.1 ∈ InvS W T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' M c →
      pr.1.2 ∈ PiNS W T π' M → W.clK T pr ∈ latticeFiniteCohomology PD T.L := by
    intro pr hy hz
    refine (h2b (W.clK T pr)).mpr ?_
    rw [hres hs1 hp2 T pr]
    simp only [InvS, LamPS, Submodule.mem_inf, Submodule.mem_comap, Submodule.restrictScalars_mem] at hy
    obtain ⟨⟨⟨hyφ, _⟩, _⟩, _⟩ := hy
    have hNl : W.Nl T (c - 1) ≤ W.N T := by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hu
      exact (W.N T).smul_mem (letE (c - 1) : LetA O n) hv
    obtain ⟨k, hk⟩ := classMapPf_φspan W T _ hNl _ hyφ
    have hk' : W.Q ^ k • (Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ h' • pr.1.1) ∈ W.N T := hk
    have hu1 : (wq : LetA O n) ^ h' * ((wq⁻¹ : (LetA O n)ˣ) : LetA O n) ^ h' = 1 := by
      rw [← mul_pow, Units.mul_inv, one_pow]
    have hcoef : W.q ^ (h' + k) = (wq : LetA O n) ^ h' * W.Q ^ k * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ h' := by
      rw [hQ, hE, mul_pow]
      linear_combination (-(W.q ^ (h' + k))) * hu1
    have hmem := (W.N T).smul_mem ((wq : LetA O n) ^ h') hk'
    rw [smul_smul, smul_smul, ← hcoef] at hmem
    have e0 : (W.φA ^ 0) W.Q = W.q := by rw [pow_zero]; exact hQ
    have hJ : ((Multiset.replicate (h' + k) 0).map fun j => (W.φA ^ j) W.Q).prod • pr.1.1 ∈ W.N T := by
      simp only [Multiset.map_replicate, Multiset.prod_replicate, e0]
      exact hmem
    have hz' : pr.1.2 ∈ Formalism.MainNotions.DeltaInvariantLattices.aN W T letπ := by
      obtain ⟨hza, _⟩ := Submodule.mem_inf.mp
        (show pr.1.2 ∈ (Formalism.MainNotions.DeltaInvariantLattices.aN W T (π' ^ M)).restrictScalars O ⊓ DelS W T from hz)
      rw [Submodule.restrictScalars_mem] at hza
      obtain ⟨u, hu, hzu⟩ := Submodule.mem_map.mp hza
      refine Submodule.mem_map.mpr ⟨((wπ : LetA O n) ^ M * letπ ^ (s' * M - 1)) • u,
        (W.N T).smul_mem _ hu, ?_⟩
      rw [← hzu]
      show (letπ : LetA O n) • (((wπ : LetA O n) ^ M * letπ ^ (s' * M - 1)) • u) = π' ^ M • u
      rw [smul_smul, hwπ]
      congr 1
      have hsM : 1 ≤ s' * M := Nat.mul_pos hs' hM
      obtain ⟨t, ht⟩ : ∃ t, s' * M = t + 1 := ⟨s' * M - 1, (Nat.sub_add_cancel hsM).symm⟩
      rw [mul_pow, ← pow_mul, ht, Nat.add_sub_cancel]
      ring
    exact h7 _ _ _ hJ hz' _
  exact classMapPf_local W T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' M c hF hγ hker hf

end Local

theorem classMapPf_MK_pos {l : ℕ} [Fact l.Prime] (K : FinExt l) (h' : ℕ) (hh' : 1 ≤ h')
    (hs : 1 ≤ sK l K) : 1 ≤ MK l K h' := by
  have h1 : (0 : ℝ) < 4 * (h' : ℝ) := by
    have : (1 : ℝ) ≤ h' := by exact_mod_cast hh'
    linarith
  have h2 : (0 : ℝ) < (sK l K : ℝ) := by
    have : (1 : ℝ) ≤ (sK l K : ℝ) := by exact_mod_cast hs
    linarith
  exact Nat.ceil_pos.mpr (div_pos h1 h2)

theorem classMapR_of_frobPiN (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : adm1 D HW F Cm) (h2 : adm2 D HW F)
    (hsK : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → 1 ≤ sK l K)
    (hF : frobPiNR D HW) : classMapR D HW := by
  intro l _ hl K LL hG π' E hp9 T h' hh' hc hj c
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hsK := hsK l hl K LL hG
  exact classMapPf_of _ T π' E (eK K) (sK l K) h' (MK l K h') c ((HW l).W_s K 1 LL hG)
    (by rw [hp]; exact hl) hsK (classMapPf_MK_pos K h' hh' hsK) hp9
    (hF l hl K LL hG π' E hp9 T h' hh' hc hj)
    ((h2 l K 1 LL hG).1 T hc).2 ((h2 l K 1 LL hG).2.1 T hc) ((h1 l K 1 LL hG).2.2.2.2.2.2.1 T hc)
    (Formalism.MainNotions.CrystallineLiftingBounds.resK_holds D HW F l K 1 LL hG)

theorem classmap_of_frobpin
    (hsK : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → 1 ≤ sK l K)
    (hF : FrobPiNStep) : ClassMapStep := by
  unfold ClassMapStep
  intro D HW F Cm CA CB CK hA
  have hA' := (show adm1 D HW F Cm ∧ adm2 D HW F ∧ _ from hA)
  exact classMapR_of_frobPiN D HW F Cm hA'.1 hA'.2.1 hsK (hF D HW F Cm CA CB CK hA)

theorem classmap_pf : Formalism.MainNotions.N.Ln34.ClassMapStep :=
  classmap_of_frobpin (fun _l _ hl K LL hG => Formalism.MainNotions.N.Ln34.frobpin_sK_pos hl K LL hG)
    Formalism.MainNotions.N.Ln34.frobPiNCondition

end Formalism.MainNotions.N.Ln34.ClassMapPf

end
