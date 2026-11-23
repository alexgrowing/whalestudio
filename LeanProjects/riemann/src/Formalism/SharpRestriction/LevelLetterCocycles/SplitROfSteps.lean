import Formalism.SharpRestriction.LevelLetterCocycles.MixedPositionHypothesis
import Formalism.SharpRestriction.LevelLetterCocycles.MapCompZero

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def WKill {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (ρ : ℕ) : Prop :=
  ∀ c : ZMod n, ∀ y ∈ NcS W T₂ c, ∃ x ∈ NcS W T₁ c, W.map F x = ((PD.p : ℕ) : O) ^ ρ • y

def KerLam {T Tp T'' : LocLat G Qp LL O} (ι : LatHom T.L Tp.L) (π : LatHom Tp.L T''.L)
    (π' Eπ : LetA O n) (h' : ℕ) : Prop :=
  Function.Injective (W.map ι) ∧
  (∀ k : ℕ, ∀ y ∈ PiNS W Tp π' k, W.map π y = 0 → ∃ x ∈ PiNS W T π' k, W.map ι x = y) ∧
  ∀ c : ZMod n,
    (∀ y ∈ LamPS W Tp Eπ h' c, W.map π y = 0 → ∃ x ∈ LamPS W T Eπ h' c, W.map ι x = y) ∧
    (∀ y ∈ NcS W Tp c, W.map π y = 0 → ∃ x ∈ NcS W T c, W.map ι x = y)

def NinLam (T : LocLat G Qp LL O) (Eπ : LetA O n) (h' : ℕ) : Prop :=
  ∀ c : ZMod n, NcS W T c ≤ LamPS W T Eπ h' c

def GradN (T : LocLat G Qp LL O) (π' : LetA O n) (σ M : ℕ) : Prop :=
  ∀ c : ZMod n, ∀ z ∈ PiNS W T π' 1 ⊓ letS W T c, ∃ k ∈ PiNS W T π' 1 ⊓ letS W T c,
    ((PD.p : ℕ) : O) ^ σ • z - (W.γD T W.gamK k - k) ∈ PiNS W T π' M

def FrobPiN (T : LocLat G Qp LL O) (π' : LetA O n) (M : ℕ) : Prop :=
  (∀ x ∈ PiNS W T π' M, W.φD T x ∈ PiNS W T π' M) ∧
    ∀ b ∈ PiNS W T π' M, ∃! x, x ∈ PiNS W T π' M ∧ W.φD T x - x = b

def GamPi (T : LocLat G Qp LL O) (π' : LetA O n) : Prop :=
  ∀ c : ZMod n, ∀ x ∈ NcS W T c, W.γD T W.gamK x - x ∈ PiNS W T π' 1 ⊓ letS W T c

def OneGen : Prop := ∃ e : W.DD W.one, Formalism.MainNotions.ElementDenominator.IsUnitGen W e

end Local

section SplitLocal

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

set_option maxHeartbeats 1000000 in

theorem split_local (W : LocWach PD LL O v n) (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L)
    (π : LatHom Tp.L W.one.L) (κ : G → T.V) (hκ : κ ∈ latticeCocycles T.L) (e : W.DD W.one)
    (π' Eπ : LetA O n) (h' M ρ σ : ℕ) (u : Oˣ)
    (hses : IsSESLat (Qp := Qp) ι π) (he : Formalism.MainNotions.ElementDenominator.IsUnitGen W e)
    (hWk : WKill W π ρ) (hKL : KerLam W ι π π' Eπ h') (hNL : NinLam W Tp Eπ h')
    (hGN : GradN W T π' σ M) (hFP : FrobPiN W T π' M) (hγp : GamPi W Tp π')
    (hmapN : ∀ x ∈ W.N T, W.map ι x ∈ W.N Tp)
    (hu : ∀ (x : W.DD Tp) (a : O), (∀ δ ∈ W.DelF, W.γD Tp δ x = x) → W.map π x = a • e →
      ∀ (y z : W.DD T) (h : (y, z) ∈ W.wachCocyclesDelta T),
        W.map ι y = W.φD Tp x - x → W.map ι z = W.γD Tp W.gamK x - x →
        W.clK T ⟨(y, z), h⟩ = ((u : O) * a) • (Submodule.Quotient.mk (⟨κ, hκ⟩ : ↥(latticeCocycles T.L)) : LatticeCohomology T.L))
    (hker : ∀ w : ↥(W.wachCocyclesDelta T), W.clK T w = 0 ↔ ∃ m : W.DD T, Formalism.MainNotions.DeltaInvariantLattices.DInv W T m ∧
      (w : W.DD T × W.DD T) = (W.φD T m - m, W.γD T W.gamK m - m)) :
    (((PD.p : ℕ) : O) ^ (ρ + σ)) • κ ∈ (⨆ c, JZ W T π' Eπ h' M c) ⊔ latticeCoboundaries T.L := by
  classical
  have h0 : ∀ y, π.f (ι.f y) = 0 := fun y => (hses.2.2.2.1 (ι.f y)).2 ⟨y, rfl⟩
  have hπι : ∀ x, W.map π (W.map ι x) = 0 := fun x => map_comp_zero W T ι π h0 x
  have heN : e ∈ W.N W.one := by rw [he.1]; exact Submodule.subset_span rfl
  have hyN : ∀ c, (letE c : LetA O n) • e ∈ NcS W W.one c := by
    intro c
    refine (mem_NcS W W.one c _).2 ⟨(W.N W.one).smul_mem _ heN, fun δ _ => ?_, ?_⟩
    · rw [γD_letE, he.2.2]
    · rw [smul_smul, Formalism.MainNotions.LiftingTheory.wmap_letE_idem]
  have hyγ : ∀ c g, W.γD W.one g ((letE c : LetA O n) • e) = (letE c : LetA O n) • e := by
    intro c g; rw [γD_letE, he.2.2]
  have hyφ : ∀ c, W.φD W.one ((letE (c - 1) : LetA O n) • e) = (letE c : LetA O n) • e := by
    intro c; rw [φD_letE, he.2.1]
  choose x hx hxπ using fun c => hWk c _ (hyN c)
  have hdπ : ∀ c, W.map π (W.γD Tp W.gamK (x c) - x c) = 0 := by
    intro c
    rw [map_sub, W.map_γ, hxπ c, map_smul, hyγ, sub_self]
  choose z hz hzι using fun c => hKL.2.1 1 _ ((hγp c (x c) (hx c)).1) (hdπ c)
  have hzlet : ∀ c, z c ∈ letS W T c := by
    intro c
    rw [mem_letS]
    apply hKL.1
    rw [map_letA_smul, hzι c]
    exact (mem_letS W Tp c _).1 (hγp c (x c) (hx c)).2
  choose k hk hk' using fun c => hGN c (z c) ⟨hz c, hzlet c⟩
  have hmO : ∀ {T₁ T₂ : LocLat G Qp LL O} (f : LatHom T₁.L T₂.L) (c : O) (y : W.DD T₁),
      W.map f (c • y) = c • W.map f y := fun f c y => LinearMap.map_smul_of_tower _ c y
  set kk : ZMod n → W.DD T := fun c => ((PD.p : ℕ) : O) ^ σ • z c - (W.γD T W.gamK (k c) - k c)
    with hkk
  have hkkM : ∀ c, kk c ∈ PiNS W T π' M := hk'
  set xb : ZMod n → W.DD Tp := fun c => ((PD.p : ℕ) : O) ^ σ • x c - W.map ι (k c) with hxb
  have hkN : ∀ c, k c ∈ W.N T := fun c => PiNS_le_N W T π' 1 (hk c).1
  have hxbN : ∀ c, xb c ∈ NcS W Tp c := by
    intro c
    obtain ⟨hxN, hxΔ, hxl⟩ := (mem_NcS W Tp c (x c)).1 (hx c)
    have hkl := (mem_letS W T c (k c)).1 (hk c).2
    have hkΔ := ((mem_PiNS W T π' 1 (k c)).1 (hk c).1).2
    refine (mem_NcS W Tp c _).2 ⟨?_, fun δ hδ => ?_, ?_⟩
    · exact (W.N Tp).sub_mem ((W.N Tp).smul_of_tower_mem _ hxN) (hmapN _ (hkN c))
    · simp only [hxb, map_sub, map_smul, hxΔ δ hδ, ← W.map_γ, hkΔ δ hδ]
    · simp only [hxb, smul_sub, ← map_letA_smul, hkl]
      rw [smul_comm, hxl]
  have hxbγ : ∀ c, W.γD Tp W.gamK (xb c) - xb c = W.map ι (kk c) := by
    intro c
    simp only [hxb, hkk, map_sub, map_smul, ← W.map_γ, hmO, hzι c, smul_sub]
    abel
  have hxbπ : ∀ c, W.map π (xb c) = ((PD.p : ℕ) : O) ^ (ρ + σ) • (letE c : LetA O n) • e := by
    intro c
    simp only [hxb, map_sub, hmO, hxπ c, hπι, sub_zero, smul_smul, ← pow_add, add_comm σ ρ]
  set xs : ZMod n → W.DD Tp := fun c => W.φD Tp (xb (c - 1)) with hxs
  have hxbNl : ∀ c, xb c ∈ W.Nl Tp c := by
    intro c
    obtain ⟨hN, -, hl⟩ := (mem_NcS W Tp c _).1 (hxbN c)
    exact Submodule.mem_map.2 ⟨xb c, hN, hl⟩
  have hxsLam : ∀ c, xs c ∈ LamPS W Tp Eπ h' c := by
    intro c
    obtain ⟨hN, hΔ, hl⟩ := (mem_NcS W Tp (c - 1) _).1 (hxbN (c - 1))
    refine (mem_LamPS W Tp Eπ h' c _).2 ⟨?_, fun δ hδ => ?_, ?_⟩
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨xb (c - 1), hxbNl (c - 1), rfl⟩)
    · simp only [hxs]; rw [← W.φγ_comm, hΔ δ hδ]
    · simp only [hxs]; rw [← φD_letE, hl]
  have hwt : ∀ c, xs c - xb c ∈ LamPS W Tp Eπ h' c :=
    fun c => Submodule.sub_mem _ (hxsLam c) (hNL c (hxbN c))
  have hwtπ : ∀ c, W.map π (xs c - xb c) = 0 := by
    intro c
    simp only [hxs, map_sub, W.map_φ, hxbπ, map_smul, hyφ, sub_self]
  choose w hw hwι using fun c => (hKL.2.2 c).1 _ (hwt c) (hwtπ c)
  have hwγ : ∀ c, W.γD T W.gamK (w c) - w c = W.φD T (kk (c - 1)) - kk c := by
    intro c
    apply hKL.1
    rw [map_sub, map_sub, W.map_φ, ← hxbγ, ← hxbγ, W.map_γ, hwι c]
    simp only [hxs, map_sub, ← W.φγ_comm]
    abel
  have hwInv : ∀ c, w c ∈ InvS W T π' Eπ h' M c := fun c =>
    (mem_InvS W T π' Eπ h' M c _).2
      ⟨hw c, by rw [hwγ c]; exact Submodule.sub_mem _ (hFP.1 _ (hkkM _)) (hkkM c)⟩
  have hγwM : ∀ c, W.γD T W.gamK (w c) - w c ∈ PiNS W T π' M :=
    fun c => ((mem_InvS W T π' Eπ h' M c _).1 (hwInv c)).2
  choose zz hzz using fun c => (hFP.2 _ (hγwM c)).exists
  have hcocmem : ∀ (a b : W.DD T), W.γD T W.gamK a - a = W.φD T b - b →
      (∀ δ ∈ W.DelF, W.γD T δ a = a) → (∀ δ ∈ W.DelF, W.γD T δ b = b) → (a, b) ∈ W.wachCocyclesDelta T := by
    intro a b hab ha hb
    show (a, b) ∈ herrZ1Δ _ _ _ _
    unfold herrZ1Δ herrCocycles
    simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.coprod_apply, Submodule.mem_iInf,
      LinearMap.sub_apply, LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.neg_apply, Prod.mk_sub_mk,
      Prod.mk_eq_zero]
    refine ⟨?_, fun δ hδ => ⟨by rw [ha δ hδ, sub_self], by rw [hb δ hδ, sub_self]⟩⟩
    rw [hab]; abel
  have hwΔ : ∀ c, ∀ δ ∈ W.DelF, W.γD T δ (w c) = w c :=
    fun c => ((mem_LamPS W T Eπ h' c _).1 (hw c)).2.1
  have hPiΔ : ∀ {j : ℕ} {y : W.DD T}, y ∈ PiNS W T π' j → ∀ δ ∈ W.DelF, W.γD T δ y = y :=
    fun hy => ((mem_PiNS W T π' _ _).1 hy).2
  have hcoc : ∀ c, (w c, zz c) ∈ W.wachCocyclesDelta T := fun c =>
    hcocmem _ _ (hzz c).2.symm (hwΔ c) (hPiΔ (hzz c).1)
  choose κc hκc using fun c =>
    Submodule.mkQ_surjective ((latticeCoboundaries T.L).comap (latticeCocycles T.L).subtype) (W.clK T ⟨(w c, zz c), hcoc c⟩)
  have hκcJ : ∀ c, ((κc c : ↥(latticeCocycles T.L)) : G → T.V) ∈ JZ W T π' Eπ h' M c := fun c =>
    Submodule.subset_span ⟨(κc c).2, w c, hwInv c, zz c, (hzz c).1, hcoc c, by
      rw [Subtype.coe_eta]; exact hκc c⟩
  set X : W.DD Tp := ∑ c, xs c with hX
  have hXΔ : ∀ δ ∈ W.DelF, W.γD Tp δ X = X := by
    intro δ hδ
    rw [hX, map_sum]
    exact Finset.sum_congr rfl fun c _ => ((mem_LamPS W Tp Eπ h' c _).1 (hxsLam c)).2.1 δ hδ
  have hXπ : W.map π X = ((PD.p : ℕ) : O) ^ (ρ + σ) • e := by
    rw [hX, map_sum]
    simp only [hxs, W.map_φ, hxbπ, map_smul, hyφ]
    rw [← Finset.smul_sum, ← Finset.sum_smul, Formalism.MainNotions.LiftingTheory.liftb_sum_letE, one_smul]
  have hshiftT : ∀ f : ZMod n → W.DD T, ∑ c, f (c - 1) = ∑ c, f c :=
    fun f => (Equiv.subRight (1 : ZMod n)).sum_comp f
  have hshiftP : ∀ f : ZMod n → W.DD Tp, ∑ c, f (c - 1) = ∑ c, f c :=
    fun f => (Equiv.subRight (1 : ZMod n)).sum_comp f
  set Wsum : W.DD T := ∑ c, w c with hWsum
  set Zc : W.DD T := ∑ c, zz c with hZc
  set Z : W.DD T := ∑ c, W.φD T (kk (c - 1)) with hZ
  have hXs : X = ∑ c, W.φD Tp (xb c) := hshiftP (fun c => W.φD Tp (xb c))
  have hYι : W.map ι (W.φD T Wsum) = W.φD Tp X - X := by
    rw [W.map_φ, hWsum, map_sum]
    simp only [hwι, Finset.sum_sub_distrib, map_sub, map_sum]
    have e1 : W.φD Tp X = ∑ c, W.φD Tp (xs c) := by rw [hX, map_sum]
    rw [e1, hXs]
  have hZι : W.map ι Z = W.γD Tp W.gamK X - X := by
    rw [hZ, map_sum, hX, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [W.map_φ, ← hxbγ, map_sub, W.φγ_comm]
  have hWΔ : ∀ δ ∈ W.DelF, W.γD T δ Wsum = Wsum := by
    intro δ hδ
    rw [hWsum, map_sum]
    exact Finset.sum_congr rfl fun c _ => hwΔ c δ hδ
  have hYΔ : ∀ δ ∈ W.DelF, W.γD T δ (W.φD T Wsum) = W.φD T Wsum := by
    intro δ hδ; rw [← W.φγ_comm, hWΔ δ hδ]
  have hZΔ : ∀ δ ∈ W.DelF, W.γD T δ Z = Z := by
    intro δ hδ
    rw [hZ, map_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [← W.φγ_comm, hPiΔ (hkkM (c - 1)) δ hδ]
  have hYZc : W.γD T W.gamK (W.φD T Wsum) - W.φD T Wsum = W.φD T Z - Z := by
    apply hKL.1
    rw [map_sub, map_sub, W.map_γ, hYι, W.map_φ, hZι]
    simp only [map_sub, W.φγ_comm]
    abel
  have hYZ : (W.φD T Wsum, Z) ∈ W.wachCocyclesDelta T := hcocmem _ _ hYZc hYΔ hZΔ
  have hclK := hu X (((PD.p : ℕ) : O) ^ (ρ + σ)) hXΔ hXπ _ Z hYZ hYι hZι
  have hZM : Z ∈ PiNS W T π' M := Submodule.sum_mem _ fun c _ => hFP.1 _ (hkkM (c - 1))
  have hγW : W.γD T W.gamK Wsum - Wsum = ∑ c, (W.γD T W.gamK (w c) - w c) := by
    rw [hWsum, map_sum, Finset.sum_sub_distrib]
  have hZcM : Zc + (W.γD T W.gamK Wsum - Wsum) ∈ PiNS W T π' M := by
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => (hzz c).1) ?_
    rw [hγW]; exact Submodule.sum_mem _ fun c _ => hγwM c
  have h1Z : W.φD T Zc - Zc = W.γD T W.gamK Wsum - Wsum := by
    rw [hZc, map_sum, ← Finset.sum_sub_distrib, hγW]
    exact Finset.sum_congr rfl fun c _ => (hzz c).2
  have hYM : W.γD T W.gamK (W.φD T Wsum) - W.φD T Wsum ∈ PiNS W T π' M := by
    rw [hYZc]; exact Submodule.sub_mem _ (hFP.1 _ hZM) hZM
  have hZeq : Z = Zc + (W.γD T W.gamK Wsum - Wsum) := by
    refine (hFP.2 _ hYM).unique ⟨hZM, hYZc.symm⟩ ⟨hZcM, ?_⟩
    have h1' : W.φD T Zc = Zc + (W.γD T W.gamK Wsum - Wsum) := by rw [← h1Z]; abel
    rw [map_add, map_sub, h1', W.φγ_comm]
    abel
  have hcob : (W.φD T Wsum - Wsum, W.γD T W.gamK Wsum - Wsum) ∈ W.wachCocyclesDelta T := by
    refine hcocmem _ _ ?_ (fun δ hδ => by rw [map_sub, ← W.φγ_comm, hWΔ δ hδ])
      (fun δ hδ => by rw [map_sub, ← W.γD_mul, mul_comm, W.γD_mul, hWΔ δ hδ])
    simp only [map_sub, W.φγ_comm]
    abel
  have hdecomp : (⟨(W.φD T Wsum, Z), hYZ⟩ : ↥(herrZ1Δ (W.γD T W.gamK) (W.φD T) W.DelF (W.γD T))) =
      ∑ c, (⟨(w c, zz c), hcoc c⟩ : ↥(herrZ1Δ (W.γD T W.gamK) (W.φD T) W.DelF (W.γD T))) + (⟨_, hcob⟩ : ↥(herrZ1Δ (W.γD T W.gamK) (W.φD T) W.DelF (W.γD T))) := by
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_sum]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_sum]
      rw [← hWsum]; abel
    · simp only [Prod.snd_add, Prod.snd_sum]
      rw [← hZc, hZeq]
  have hcob0 : W.clK T (⟨_, hcob⟩ : ↥(herrZ1Δ (W.γD T W.gamK) (W.φD T) W.DelF (W.γD T))) = 0 := (hker _).2 ⟨Wsum, hWΔ, rfl⟩
  have hsum : W.clK T ⟨(W.φD T Wsum, Z), hYZ⟩ =
      Submodule.mkQ ((latticeCoboundaries T.L).comap (latticeCocycles T.L).subtype) (∑ c, κc c) := by
    have hsum0 : W.clK T ⟨(W.φD T Wsum, Z), hYZ⟩ =
        W.clK T (∑ c, (⟨(w c, zz c), hcoc c⟩ : ↥(herrZ1Δ (W.γD T W.gamK) (W.φD T) W.DelF (W.γD T))) + (⟨_, hcob⟩ : ↥(herrZ1Δ (W.γD T W.gamK) (W.φD T) W.DelF (W.γD T)))) := congrArg (W.clK T) hdecomp
    rw [hsum0, map_add, map_sum, hcob0, add_zero, map_sum]
    exact Finset.sum_congr rfl fun c _ => (hκc c).symm
  have key : Submodule.mkQ ((latticeCoboundaries T.L).comap (latticeCocycles T.L).subtype)
      ((((PD.p : ℕ) : O) ^ (ρ + σ)) • (⟨κ, hκ⟩ : ↥(latticeCocycles T.L))) =
      Submodule.mkQ ((latticeCoboundaries T.L).comap (latticeCocycles T.L).subtype) (((↑u⁻¹ : O)) • ∑ c, κc c) := by
    rw [map_smul, map_smul, ← hsum, hclK, smul_smul, ← mul_assoc, Units.inv_mul, one_mul]
    rfl
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at key
  have hB : ((((((PD.p : ℕ) : O) ^ (ρ + σ)) • (⟨κ, hκ⟩ : ↥(latticeCocycles T.L)) -
      ((↑u⁻¹ : O)) • ∑ c, κc c : ↥(latticeCocycles T.L)) : G → T.V)) ∈ latticeCoboundaries T.L := key
  have hsplit : (((PD.p : ℕ) : O) ^ (ρ + σ)) • κ =
      ((↑u⁻¹ : O)) • (∑ c, ((κc c : ↥(latticeCocycles T.L)) : G → T.V)) +
        ((((((PD.p : ℕ) : O) ^ (ρ + σ)) • (⟨κ, hκ⟩ : ↥(latticeCocycles T.L)) -
          ((↑u⁻¹ : O)) • ∑ c, κc c : ↥(latticeCocycles T.L)) : G → T.V)) := by
    simp only [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_sum]
    abel
  rw [hsplit]
  refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun c _ => ?_)) hB
  exact (le_iSup (fun c => JZ W T π' Eπ h' M c) c) (hκcJ c)

end SplitLocal

section Record

def wKillR (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL)),
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E →
    ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (h' : ℕ),
      IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → F.Onto →
      (∀ τ, JumpsInV ((D.loc l).PD K) T₁.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      WKill ((HW l).W K 1 LL hG) F (rhoA l (eK K) h')

def kerLamR (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL)),
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E →
    ∀ (T Tp T'' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L T''.L)
      (h' : ℕ), IsSESLat (Qp := ℚ_[l]) ι π → IsCrys ((D.loc l).PD K) T.ρ →
      IsCrys ((D.loc l).PD K) Tp.ρ → IsCrys ((D.loc l).PD K) T''.ρ →
      (∀ τ, JumpsInV ((D.loc l).PD K) Tp.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      KerLam ((HW l).W K 1 LL hG) ι π π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h'

def ninLamR (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL)),
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E →
    ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (h' : ℕ), IsCrys ((D.loc l).PD K) T.ρ →
      (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      NinLam ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h'

def gradNR (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL)),
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E →
    ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T.ρ →
      GradN ((HW l).W K 1 LL hG) T π' (sigA l (sK l K) h') (MK l K h')

def frobPiNR (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL)),
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E →
    ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T.ρ →
      (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      FrobPiN ((HW l).W K 1 LL hG) T π' (MK l K h')

def gamPiR (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL)),
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E →
    ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys ((D.loc l).PD K) T.ρ →
      GamPi ((HW l).W K 1 LL hG) T π'

def oneGenR (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL),
    OneGen ((HW l).W K 1 LL hG)

def extOfR (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T.ρ →
    (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
    ∀ κ ∈ latticeFiniteCocycles ((D.loc l).PD K) T.L,
      ∃ (Tp : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T.L Tp.L)
        (π : LatHom Tp.L ((HW l).W K 1 LL hG).one.L),
        Formalism.MainNotions.LiftingTheory.IsExtOf ((HW l).W K 1 LL hG) ι π κ ∧ IsCrys ((D.loc l).PD K) Tp.ρ ∧
        IsCrys ((D.loc l).PD K) ((HW l).W K 1 LL hG).one.ρ ∧
        ∀ τ, JumpsInV ((D.loc l).PD K) Tp.ρ τ (Set.Icc (-(h' : ℤ)) h')

set_option maxHeartbeats 2000000 in

theorem splitR_of_steps (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h2 : adm2 D HW F) (h2e : HerrClassMapsLocal D HW F) (hE : extOfR D HW) (hW : wKillR D HW)
    (hK : kerLamR D HW) (hN : ninLamR D HW) (hGr : gradNR D HW) (hF : frobPiNR D HW)
    (hγ : gamPiR D HW) (h1 : oneGenR D HW) : splitR D HW := by
  classical
  intro l _ hl K LL hG π' E hπ T h' hh' hc hj κ hκ
  obtain ⟨Tp, ι, π, hext, hcp, hco, hjp⟩ := hE l hl K LL hG T h' hh' hc hj κ hκ
  obtain ⟨e, he⟩ := h1 l hl K LL hG
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [hp]; exact hl
  obtain ⟨u, hu⟩ := (h2e l K 1 LL hG).2.2.2 hs1 hp2 T Tp ι π hc hcp κ hκ.1 hext e he
  have hP := ((h2 l K 1 LL hG).1 T hc).2 hs1 hp2
  have : NeZero (finrank ℚ_[l] ↥(K0 K)) := ⟨by
    have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    have hle : K0 K ≤ K.1 := inf_le_left
    have : FiniteDimensional ℚ_[l] ↥(K0 K) :=
      FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
        (IntermediateField.inclusion_injective hle)
    exact Module.finrank_pos.ne'⟩
  have hmain := split_local ((HW l).W K 1 LL hG) T Tp ι π κ hκ.1 e π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h'
    (MK l K h') (rhoA l (eK K) h') (sigA l (sK l K) h') u hext.1 he
    (hW l hl K LL hG π' E hπ Tp _ π h' hcp hco hext.1.2.2.1 hjp)
    (hK l hl K LL hG π' E hπ T Tp _ ι π h' hext.1 hc hcp hco hjp)
    (hN l hl K LL hG π' E hπ Tp h' hcp hjp)
    (hGr l hl K LL hG π' E hπ T h' hh' hc)
    (hF l hl K LL hG π' E hπ T h' hh' hc hj)
    (hγ l hl K LL hG π' E hπ Tp hcp)
    (fun x hx => ((HW l).W K 1 LL hG).map_N ι hc hcp x hx) hu hP.2
  have e1 : ((l ^ (rhoA l (eK K) h' + sigA l (sK l K) h') : ℕ) : ↥(OL LL)) =
      ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ^ (rhoA l (eK K) h' + sigA l (sK l K) h') := by
    rw [hp]; push_cast; rfl
  rw [← Nat.cast_smul_eq_nsmul ↥(OL LL), e1]
  exact hmain

end Record

end Formalism.MainNotions.N.Ln34

end
