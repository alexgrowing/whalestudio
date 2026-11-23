import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgCechSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgSFreeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgFiltSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CechHcSubsingletonOfBij
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGradedSubquot
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace KHTheoremS

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem cechHc_subsingleton_of_cochains {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ)
    (h : Subsingleton (KH.CechC S ι M n)) : Subsingleton (KH.cechHc ι 𝓜 c n) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Subtype.ext (Subsingleton.elim (x : KH.CechC S ι M n) y)]

theorem cechHc_punit (c : K → ℤ) (n : ℕ) :
    Subsingleton (KH.cechHc ι (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) c n) :=
  cechHc_subsingleton_of_cochains _ c n
    ⟨fun _ _ => funext fun _ => Subsingleton.elim (α := LocalizedModule _ PUnit) _ _⟩

theorem exists_mem_of_surjective {M M'' : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] [AddCommGroup M''] [Module (MRingOver S ι) M''] [Module S M'']
    [IsScalarTower S (MRingOver S ι) M''] {𝓜 : (K → ℤ) → Submodule S M} {𝓜'' : (K → ℤ) → Submodule S M''}
    (h𝓜 : KH.IsMGraded S ι 𝓜) (h𝓜'' : KH.IsMGraded S ι 𝓜'') {h : M →ₗ[MRingOver S ι] M''}
    (hh : KH.IsMGradedMap S ι 𝓜 𝓜'' h) (hs : Function.Surjective h) {c : K → ℤ} {m'' : M''}
    (hm : m'' ∈ 𝓜'' c) : ∃ m ∈ 𝓜 c, h m = m'' := by
  classical
  obtain ⟨x, rfl⟩ := hs m''
  have key : ∃ y ∈ 𝓜 c, h x - h y ∈ ⨆ (j) (_ : j ≠ c), 𝓜'' j := by
    have hx : x ∈ ⨆ j, 𝓜 j := by
      rw [h𝓜.1.submodule_iSup_eq_top]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (motive := fun x => ∃ y ∈ 𝓜 c, h x - h y ∈ ⨆ (j) (_ : j ≠ c), 𝓜'' j)
      𝓜 hx ?_ ?_ ?_
    · intro j x hx
      by_cases hj : j = c
      · subst hj
        exact ⟨x, hx, by rw [sub_self]; exact zero_mem _⟩
      · refine ⟨0, zero_mem _, ?_⟩
        rw [map_zero, sub_zero]
        exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (hh j x hx))
    · exact ⟨0, zero_mem _, by rw [map_zero, sub_zero]; exact zero_mem _⟩
    · intro x₁ x₂ h₁ h₂
      obtain ⟨y₁, hy₁, e₁⟩ := h₁
      obtain ⟨y₂, hy₂, e₂⟩ := h₂
      refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_⟩
      have : h (x₁ + x₂) - h (y₁ + y₂) = (h x₁ - h y₁) + (h x₂ - h y₂) := by
        simp only [map_add]
        abel
      rw [this]
      exact add_mem e₁ e₂
  obtain ⟨y, hy, hd⟩ := key
  have hc : h x - h y ∈ 𝓜'' c := sub_mem hm (hh c y hy)
  have h0 : h x - h y = 0 := Submodule.disjoint_def.mp (h𝓜''.1.submodule_iSupIndep c) _ hc hd
  exact ⟨y, hy, (sub_eq_zero.mp h0).symm⟩

abbrev lmap {M N : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N] [Module (MRingOver S ι) N]
    (T : Submonoid (MRingOver S ι)) (g : M →ₗ[MRingOver S ι] N) :
    LocalizedModule T M →ₗ[MRingOver S ι] LocalizedModule T N :=
  IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M) (LocalizedModule.mkLinearMap T N) g

theorem lmap_mk {M N : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N] {T : Submonoid (MRingOver S ι)} (g : M →ₗ[MRingOver S ι] N) (m : M) (t : T) :
    lmap T g (LocalizedModule.mk m t) = LocalizedModule.mk (g m) t := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.map_mk', ← IsLocalizedModule.mk_eq_mk']

theorem cechMap_apply {M N : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N] (g : M →ₗ[MRingOver S ι] N) (n : ℕ) (z : KH.CechC S ι M n) (I : KH.Cell K ι n) :
    KH.cechMap S ι g n z I = lmap (KH.cellMon S I.1) g (z I) := rfl

theorem cellRes_locMap {M N : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N] (g : M →ₗ[MRingOver S ι] N) (J I : ∀ k, Finset (ι k))
    (x : LocalizedModule (KH.cellMon S J) M) :
    KH.cellRes S N J I (lmap (KH.cellMon S J) g x) =
      lmap (KH.cellMon S I) g (KH.cellRes S M J I x) := by
  by_cases h : KH.cellMon S J ≤ KH.cellMon S I
  · induction x using LocalizedModule.induction_on with
    | h m t =>
      rw [lmap_mk, GenTwistGenerated.cellRes_mk h, GenTwistGenerated.cellRes_mk h,
        lmap_mk]
  · unfold KH.cellRes
    rw [dif_neg h, dif_neg h, LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

theorem cechD_cechMap {M N : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N] (g : M →ₗ[MRingOver S ι] N) (n : ℕ) (z : KH.CechC S ι M n) :
    KH.cechD S ι N n (KH.cechMap S ι g n z) = KH.cechMap S ι g (n + 1) (KH.cechD S ι M n z) := by
  funext I
  rw [cechMap_apply]
  simp only [KH.cechD, LinearMap.pi_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hI
  · change KH.faceSign I.1 k i • KH.cellRes S N _ I.1 (KH.cechMap S ι g n z ⟨_, hI⟩) =
      lmap (KH.cellMon S I.1) g (KH.faceSign I.1 k i • KH.cellRes S M _ I.1 (z ⟨_, hI⟩))
    exact (congrArg (KH.faceSign I.1 k i • ·) (cellRes_locMap g (Function.update I.1 k ((I.1 k).erase i)) I.1
      (z ⟨_, hI⟩))).trans (map_zsmul (lmap (KH.cellMon S I.1) g) _ _).symm
  · simp only [LinearMap.zero_apply, map_zero]

theorem locMap_mem_locPart {M N : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] [AddCommGroup N] [Module (MRingOver S ι) N] [Module S N]
    [IsScalarTower S (MRingOver S ι) N] {𝓜 : (K → ℤ) → Submodule S M} {𝓝 : (K → ℤ) → Submodule S N}
    {g : M →ₗ[MRingOver S ι] N} (hg : KH.IsMGradedMap S ι 𝓜 𝓝 g) {T : Submonoid (MRingOver S ι)} {c : K → ℤ}
    {x : LocalizedModule T M} (hx : x ∈ KH.locPart ι 𝓜 T c) : lmap T g x ∈ KH.locPart ι 𝓝 T c := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    rw [lmap_mk]
    exact GenSESStep.mk_mem_locPart _ t a ht (hg _ m hm)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul s x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ s hx

theorem cechMap_mem_cechZc {M N : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] [AddCommGroup N] [Module (MRingOver S ι) N] [Module S N]
    [IsScalarTower S (MRingOver S ι) N] {𝓜 : (K → ℤ) → Submodule S M} {𝓝 : (K → ℤ) → Submodule S N}
    {g : M →ₗ[MRingOver S ι] N} (hg : KH.IsMGradedMap S ι 𝓜 𝓝 g) {c : K → ℤ} {n : ℕ} {z : KH.CechC S ι M n}
    (hz : z ∈ KH.cechZc ι 𝓜 c n) : KH.cechMap S ι g n z ∈ KH.cechZc ι 𝓝 c n := by
  obtain ⟨h1, h2⟩ := hz
  refine ⟨Submodule.mem_pi.mpr fun I _ => ?_, LinearMap.mem_ker.mpr ?_⟩
  · rw [cechMap_apply]
    exact locMap_mem_locPart hg (Submodule.mem_pi.mp h1 I (Set.mem_univ _))
  · rw [cechD_cechMap, LinearMap.mem_ker.mp h2, map_zero]

theorem const_mem_cechZc {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} {c : K → ℤ} {m : M} (hm : m ∈ 𝓜 c) :
    (fun _ => LocalizedModule.mk m 1 : KH.CechC S ι M 0) ∈ KH.cechZc ι 𝓜 c 0 := by
  refine ⟨Submodule.mem_pi.mpr fun I _ => ?_, LinearMap.mem_ker.mpr ?_⟩
  · have e : (c + fun k => (((0 : K → ℕ) k : ℕ) : ℤ)) = c := by
      funext k
      simp
    exact GenSESStep.mk_mem_locPart (c := c) m 1 0 isMultiHomog_one_zero (by rw [e]; exact hm)
  · funext I
    obtain ⟨J₁, J₂, h₁, h₂, σ, -, hd⟩ := GenTwistGenerated.cechD_zero_apply (S := S) (M := M) I
    rw [hd, GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono h₁),
      GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono h₂)]
    exact (congrArg (σ • ·) (sub_self _)).trans (zsmul_zero σ)

theorem devissage (hPF : KH.PrimeFiltStatement) (hS : IsNoetherianRing S)
    (C : ∀ (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
      [IsScalarTower S (MRingOver S ι) M], ((K → ℤ) → Submodule S M) → Prop)
    (h0 : C PUnit (fun _ => ⊥))
    (hext : ∀ (M' : Type) [AddCommGroup M'] [Module (MRingOver S ι) M'] [Module S M']
      [IsScalarTower S (MRingOver S ι) M'] (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
      [IsScalarTower S (MRingOver S ι) M] (M'' : Type) [AddCommGroup M''] [Module (MRingOver S ι) M'']
      [Module S M''] [IsScalarTower S (MRingOver S ι) M'']
      (𝓜' : (K → ℤ) → Submodule S M') (𝓜 : (K → ℤ) → Submodule S M) (𝓜'' : (K → ℤ) → Submodule S M'')
      (g : M' →ₗ[MRingOver S ι] M) (h : M →ₗ[MRingOver S ι] M''),
      KH.IsMGraded S ι 𝓜' → KH.IsMGraded S ι 𝓜 → KH.IsMGraded S ι 𝓜'' →
      KH.IsMGradedMap S ι 𝓜' 𝓜 g → KH.IsMGradedMap S ι 𝓜 𝓜'' h →
      Function.Injective g → Function.Surjective h → LinearMap.range g = LinearMap.ker h →
      C M' 𝓜' → C M'' 𝓜'' → C M 𝓜)
    (hq : ∀ 𝔭 : Ideal (MRingOver S ι), 𝔭.IsPrime → IsMultiHomogIdeal 𝔭 → ∀ e : K → ℤ,
      C (MRingOver S ι ⧸ 𝔭) (fun d => KH.quotPart S 𝔭 (d + e)))
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (hfin : Module.Finite (MRingOver S ι) M) (hgr : KH.IsMGraded S ι 𝓜) :
    C M 𝓜 := by

  have hiso : ∀ (A : Type) [AddCommGroup A] [Module (MRingOver S ι) A] [Module S A]
      [IsScalarTower S (MRingOver S ι) A] (B : Type) [AddCommGroup B] [Module (MRingOver S ι) B] [Module S B]
      [IsScalarTower S (MRingOver S ι) B] (𝓐 : (K → ℤ) → Submodule S A) (𝓑 : (K → ℤ) → Submodule S B)
      (g : A →ₗ[MRingOver S ι] B), KH.IsMGraded S ι 𝓐 → KH.IsMGraded S ι 𝓑 → KH.IsMGradedMap S ι 𝓐 𝓑 g →
      Function.Injective g → Function.Surjective g → C A 𝓐 → C B 𝓑 := by
    intro A _ _ _ _ B _ _ _ _ 𝓐 𝓑 g hA hB hg hinj hsurj hC
    refine hext A B PUnit 𝓐 𝓑 (fun _ => ⊥) g 0 hA hB GroundTheory.Heights₂.Heights.HilbertSamuel.isMGraded_punit hg
      (fun _ _ _ => Submodule.zero_mem _) hinj (fun _ => ⟨0, Subsingleton.elim _ _⟩) ?_ hC h0
    rw [LinearMap.range_eq_top.2 hsurj, LinearMap.ker_zero]
  obtain ⟨r, m, c, 𝔭, hm, h𝔭, hcol, hspan⟩ := hPF S K ι M 𝓜 hS hfin hgr
  let G : ℕ → Set M := fun j => m '' {l | (l : ℕ) < j}
  let F : ℕ → Submodule (MRingOver S ι) M := fun j => Submodule.span _ (G j)
  have hGh : ∀ j, ∀ x ∈ G j, ∃ c', x ∈ 𝓜 c' := by
    rintro j _ ⟨l, -, rfl⟩
    exact ⟨c l, hm l⟩
  have hFmono : ∀ {i j : ℕ}, i ≤ j → F i ≤ F j := fun hij =>
    Submodule.span_mono (Set.image_mono fun l (hl : (l : ℕ) < _) => lt_of_lt_of_le hl hij)
  have hgrF : ∀ j, KH.IsMGraded S ι (subGrading 𝓜 (F j)) := fun j =>
    (GradedSubquot.proof S K ι M 𝓜 (G j) (G j) hgr (hGh j) (hGh j) le_rfl).1
  have key : ∀ j ≤ r, C (F j) (subGrading 𝓜 (F j)) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hF0 : F 0 = ⊥ := by simp [F, G]
      refine hiso PUnit (F 0) _ _ 0 GroundTheory.Heights₂.Heights.HilbertSamuel.isMGraded_punit (hgrF 0)
        (fun _ _ _ => Submodule.zero_mem _) (fun _ _ _ => Subsingleton.elim _ _) (fun y => ⟨0, ?_⟩) h0
      have hy : (y : M) ∈ (⊥ : Submodule (MRingOver S ι) M) := by
        rw [← hF0]
        exact y.2
      exact (Subtype.ext ((Submodule.mem_bot _).1 hy)).symm
    | succ j ih =>
      intro hj
      have hCj := ih (Nat.le_of_succ_le hj)
      let l : Fin r := ⟨j, hj⟩
      let L : Submodule (MRingOver S ι) (F (j + 1)) := (F j).comap (F (j + 1)).subtype
      have hq' := (GradedSubquot.proof S K ι M 𝓜 (G j) (G (j + 1)) hgr (hGh j) (hGh (j + 1))
        (hFmono (Nat.le_succ j))).2
      have hml : m l ∈ F (j + 1) := Submodule.subset_span ⟨l, Nat.lt_succ_self j, rfl⟩

      let ψ : MRingOver S ι →ₗ[MRingOver S ι] (F (j + 1) ⧸ L) :=
        LinearMap.toSpanSingleton _ _ (L.mkQ ⟨m l, hml⟩)
      have hψ : ∀ p, ψ p = L.mkQ (p • ⟨m l, hml⟩) := fun p => (L.mkQ.map_smul p _).symm
      have hker : ∀ p, ψ p = 0 ↔ p ∈ 𝔭 l := by
        intro p
        rw [hψ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hcol l p
      let φ : (MRingOver S ι ⧸ 𝔭 l) →ₗ[MRingOver S ι] (F (j + 1) ⧸ L) :=
        (𝔭 l).liftQ ψ fun p hp => (LinearMap.mem_ker).2 ((hker p).2 hp)
      have hφ : ∀ p, φ (Ideal.Quotient.mk (𝔭 l) p) = ψ p := fun _ => rfl
      have hinj : Function.Injective φ := LinearMap.ker_eq_bot.1
        (Submodule.ker_liftQ_eq_bot _ _ _ fun p hp => (hker p).1 (LinearMap.mem_ker.1 hp))

      have hdec : ∀ y ∈ F (j + 1), ∃ p : MRingOver S ι, y - p • m l ∈ F j := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨l', hl', rfl⟩ := hx
          rcases Nat.lt_succ_iff_lt_or_eq.1 hl' with h | h
          · exact ⟨0, by rw [zero_smul, sub_zero]; exact Submodule.subset_span ⟨l', h, rfl⟩⟩
          · exact ⟨1, by rw [one_smul, show l' = l from Fin.ext h, sub_self]; exact (F j).zero_mem⟩
        | zero => exact ⟨0, by rw [zero_smul, sub_zero]; exact (F j).zero_mem⟩
        | add x y _ _ hx hy =>
          obtain ⟨p, hp⟩ := hx
          obtain ⟨p', hp'⟩ := hy
          refine ⟨p + p', ?_⟩
          have : x + y - (p + p') • m l = (x - p • m l) + (y - p' • m l) := by rw [add_smul]; abel
          rw [this]
          exact (F j).add_mem hp hp'
        | smul a x _ hx =>
          obtain ⟨p, hp⟩ := hx
          refine ⟨a * p, ?_⟩
          rw [mul_smul, ← smul_sub]
          exact (F j).smul_mem a hp
      have hsurj : Function.Surjective φ := by
        intro q
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective L q
        obtain ⟨p, hp⟩ := hdec y y.2
        refine ⟨Ideal.Quotient.mk (𝔭 l) p, ?_⟩
        rw [hφ, hψ, Submodule.mkQ_apply, Submodule.Quotient.eq]
        show ((p • ⟨m l, hml⟩ - y : F (j + 1)) : M) ∈ F j
        rw [Submodule.coe_sub, Submodule.coe_smul, ← neg_sub]
        exact (F j).neg_mem hp

      have hA := H1VanishingDevissage.isMGraded_shift (QuotPartGraded.proof S K ι (𝔭 l) (h𝔭 l).2.1) (-c l)
      have hG : KH.IsMGradedMap S ι (fun d => KH.quotPart S (𝔭 l) (d + -c l))
          (quotGrading (subGrading 𝓜 (F (j + 1))) L) φ := by
        intro d x hx
        refine (Submodule.span_le (p := (quotGrading (subGrading 𝓜 (F (j + 1))) L d).comap
          (φ.restrictScalars S))).2 ?_ hx
        rintro _ ⟨p, ⟨h0, hp⟩, rfl⟩
        refine ⟨p • ⟨m l, hml⟩, ?_, (hψ p).symm⟩
        have h := hgr.2 _ (c l) p (m l) hp (hm l)
        have hd : c l + (fun k => (((d + -c l) k).toNat : ℤ)) = d := by
          funext k
          have := h0 k
          simp only [Pi.add_apply, Pi.neg_apply] at this ⊢
          rw [Int.toNat_of_nonneg this]
          ring
        rw [hd] at h
        exact h
      have hCq := hiso _ _ _ _ φ hA hq' hG hinj hsurj (hq (𝔭 l) (h𝔭 l).1 (h𝔭 l).2.1 (-c l))
      let g := Submodule.inclusion (hFmono (Nat.le_succ j))
      have hex : LinearMap.range g = LinearMap.ker L.mkQ := by
        rw [Submodule.range_inclusion, Submodule.ker_mkQ]
      have hgG : KH.IsMGradedMap S ι (subGrading 𝓜 (F j)) (subGrading 𝓜 (F (j + 1))) g := fun _ _ hx => hx
      have hhG : KH.IsMGradedMap S ι (subGrading 𝓜 (F (j + 1))) (quotGrading (subGrading 𝓜 (F (j + 1))) L)
          L.mkQ := fun _ _ hx => Submodule.mem_map_of_mem hx
      exact hext _ _ _ _ _ _ g L.mkQ (hgrF j) (hgrF (j + 1)) hq' hgG hhG
        (Submodule.inclusion_injective _) (Submodule.mkQ_surjective _) hex hCj hCq
  have hFr : F r = ⊤ := by
    rw [← hspan]
    simp [F, G]
  exact hiso _ M _ 𝓜 (F r).subtype (hgrF r) hgr (fun _ _ hx => hx) (Submodule.injective_subtype _)
    (fun y => ⟨⟨y, hFr ▸ Submodule.mem_top⟩, rfl⟩) (key r le_rfl)

def idealSub (V : Ideal (MRingOver S ι)) :
    Submodule (MRingOver S ι) (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) :=
  Submodule.map (Submodule.mkQ ⊥) V

def quotMap (V : Ideal (MRingOver S ι)) :
    (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) →ₗ[MRingOver S ι] MRingOver S ι ⧸ V :=
  Submodule.liftQ ⊥ (Submodule.mkQ V) (by simp)

theorem bot_isMultiHomogIdeal : IsMultiHomogIdeal (⊥ : Ideal (MRingOver S ι)) :=
  ⟨∅, fun _ h => absurd h (Set.notMem_empty _), by simp⟩

theorem quotSES (V : Ideal (MRingOver S ι)) (hV : IsMultiHomogIdeal V) (e : K → ℤ) :
    KH.IsMGraded S ι (subGrading (fun d => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (d + e)) (idealSub V)) ∧
    KH.IsMGraded S ι (fun d => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (d + e)) ∧
    KH.IsMGraded S ι (fun d => KH.quotPart S V (d + e)) ∧
    KH.IsMGradedMap S ι (subGrading (fun d => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (d + e)) (idealSub V))
      (fun d => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (d + e)) (idealSub V).subtype ∧
    KH.IsMGradedMap S ι (fun d => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (d + e))
      (fun d => KH.quotPart S V (d + e)) (quotMap V) ∧
    Function.Injective (idealSub V).subtype ∧ Function.Surjective (quotMap V) ∧
    LinearMap.range (idealSub V).subtype = LinearMap.ker (quotMap V) := by
  have hF := H1VanishingDevissage.isMGraded_shift (QuotPartGraded.proof S K ι ⊥ bot_isMultiHomogIdeal) e
  refine ⟨?_, hF, H1VanishingDevissage.isMGraded_shift (QuotPartGraded.proof S K ι V hV) e, fun _ _ hx => hx,
    ?_, Submodule.injective_subtype _, ?_, ?_⟩
  · obtain ⟨T, hT, rfl⟩ := hV
    have hN : idealSub (Ideal.span T) =
        Submodule.span (MRingOver S ι) (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) '' T) := by
      rw [idealSub, Ideal.span, Submodule.map_span]
      rfl
    have hH : ∀ x ∈ Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) '' T,
        ∃ c', x ∈ KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c' + e) := by
      rintro _ ⟨f, hf, rfl⟩
      obtain ⟨a, ha⟩ := hT f hf
      refine ⟨(fun k => (a k : ℤ)) - e, ?_⟩
      rw [sub_add_cancel]
      refine Submodule.subset_span ⟨f, ⟨fun k => Int.natCast_nonneg _, ?_⟩, rfl⟩
      have : (fun k => ((a k : ℤ)).toNat) = a := funext fun k => Int.toNat_natCast _
      rw [this]
      exact ha
    rw [hN]
    exact (GradedSubquot.proof S K ι _ _ _ _ hF hH hH le_rfl).1
  · intro d x hx
    refine (Submodule.span_le (p := (KH.quotPart S V (d + e)).comap ((quotMap V).restrictScalars S))).2 ?_ hx
    rintro _ ⟨p, hp, rfl⟩
    exact Submodule.subset_span ⟨p, hp, rfl⟩
  · intro y
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective V y
    exact ⟨Submodule.Quotient.mk p, rfl⟩
  · rw [Submodule.range_subtype, quotMap, Submodule.ker_liftQ, Submodule.ker_mkQ, idealSub]

theorem idealSub_finite (hS : IsNoetherianRing S) (V : Ideal (MRingOver S ι)) :
    Module.Finite (MRingOver S ι) (idealSub V) := by
  have : IsNoetherianRing (MRingOver S ι) := inferInstance
  have : IsNoetherian (MRingOver S ι) (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) := inferInstance
  exact Module.IsNoetherian.finite _ _

end KHTheoremS

theorem KHCechTop.full : KH.CechTopStatement := by
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 c n hn
  refine KHTheoremS.cechHc_subsingleton_of_cochains 𝓜 c n ⟨fun _ _ => funext fun I => ?_⟩
  exfalso
  have hle : ∑ k, ((I.1 k).card - 1) ≤ ∑ k, (Fintype.card (ι k) - 1) :=
    Finset.sum_le_sum fun k _ => Nat.sub_le_sub_right (Finset.card_le_univ _) 1
  rw [I.2.2] at hle
  omega

end

end GroundTheory.Heights₂.Heights.Kleiman
