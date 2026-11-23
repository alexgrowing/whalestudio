import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechMapDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace KHCechSES

set_option linter.unusedSectionVars false

theorem finite_of_ker_le {S : Type} [CommRing S] [IsNoetherianRing S] {X E Y : Type*} [AddCommGroup X] [Module S X]
    [AddCommGroup E] [Module S E] [AddCommGroup Y] [Module S Y] [Module.Finite S Y]
    (π : E →ₗ[S] X) (hπ : Function.Surjective π) (ε : E →ₗ[S] Y) (A : Submodule S X) (hA : A.FG)
    (hk : ∀ e, ε e = 0 → π e ∈ A) : Module.Finite S X := by
  have hle : LinearMap.ker ε ≤ LinearMap.ker (A.mkQ ∘ₗ π) := fun e he => by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hk e he
  have hs : Function.Surjective
      ((LinearMap.ker ε).liftQ (A.mkQ ∘ₗ π) hle ∘ₗ ε.quotKerEquivRange.symm.toLinearMap) := by
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective A x
    obtain ⟨e, rfl⟩ := hπ x
    refine ⟨ε.quotKerEquivRange (Submodule.Quotient.mk e), ?_⟩
    simp
  have : IsNoetherian S Y := isNoetherian_of_isNoetherianRing_of_finite S Y
  have : Module.Finite S (X ⧸ A) := Module.Finite.of_surjective _ hs
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker A.mkQ ?_ ?_⟩
  · rw [Submodule.map_top, Submodule.range_mkQ]
    exact Module.Finite.fg_top
  · rwa [top_inf_eq, Submodule.ker_mkQ]

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

section General

variable {M N : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] [AddCommGroup N] [Module (MRingOver S ι) N] [Module S N]
  [IsScalarTower S (MRingOver S ι) N]

theorem mem_cechCc_iff {𝓜 : (K → ℤ) → Submodule S M} {c : K → ℤ} {n : ℕ} {x : KH.CechC S ι M n} :
    x ∈ KH.cechCc ι 𝓜 c n ↔ ∀ I, x I ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) c := by
  simp [KH.cechCc, Submodule.mem_pi]

theorem lmap_injective {T : Submonoid (MRingOver S ι)} {f : M →ₗ[MRingOver S ι] N}
    (hf : Function.Injective f) : Function.Injective (KHTheoremS.lmap T f) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  induction x using LocalizedModule.induction_on with
  | h m t =>
    rw [KHTheoremS.lmap_mk, ← LocalizedModule.zero_mk t, LocalizedModule.mk_eq] at hx
    obtain ⟨u, hu⟩ := hx
    rw [← LocalizedModule.zero_mk t, LocalizedModule.mk_eq]
    refine ⟨u, hf ?_⟩
    simp only [Submonoid.smul_def, smul_zero, map_smul, map_zero] at hu ⊢
    exact hu

theorem cechMap_injective {f : M →ₗ[MRingOver S ι] N} (hf : Function.Injective f) (n : ℕ) :
    Function.Injective (KH.cechMap S ι f n) := fun x y hxy =>
  funext fun I => lmap_injective hf (by
    have := congrFun hxy I
    rwa [KHTheoremS.cechMap_apply, KHTheoremS.cechMap_apply] at this)

theorem locPart_lift {𝓜 : (K → ℤ) → Submodule S M} {𝓝 : (K → ℤ) → Submodule S N}
    (h𝓜 : KH.IsMGraded S ι 𝓜) (h𝓝 : KH.IsMGraded S ι 𝓝) {f : M →ₗ[MRingOver S ι] N}
    (hf : KH.IsMGradedMap S ι 𝓜 𝓝 f) (hs : Function.Surjective f) {T : Submonoid (MRingOver S ι)} {c : K → ℤ}
    {x : LocalizedModule T N} (hx : x ∈ KH.locPart ι 𝓝 T c) :
    ∃ y ∈ KH.locPart ι 𝓜 T c, KHTheoremS.lmap T f y = x := by
  obtain ⟨m, t, a, ht, hm, rfl⟩ := GenSESStep.locPart_normal h𝓝 hx
  obtain ⟨y, hy, rfl⟩ := KHTheoremS.exists_mem_of_surjective h𝓜 h𝓝 hf hs hm
  exact ⟨_, GenSESStep.mk_mem_locPart y t a ht hy, KHTheoremS.lmap_mk f y t⟩

theorem cechMap_lift {𝓜 : (K → ℤ) → Submodule S M} {𝓝 : (K → ℤ) → Submodule S N}
    (h𝓜 : KH.IsMGraded S ι 𝓜) (h𝓝 : KH.IsMGraded S ι 𝓝) {f : M →ₗ[MRingOver S ι] N}
    (hf : KH.IsMGradedMap S ι 𝓜 𝓝 f) (hs : Function.Surjective f) {c : K → ℤ} {n : ℕ}
    {x : KH.CechC S ι N n} (hx : x ∈ KH.cechCc ι 𝓝 c n) :
    ∃ y ∈ KH.cechCc ι 𝓜 c n, KH.cechMap S ι f n y = x := by
  have := fun I : KH.Cell K ι n => locPart_lift h𝓜 h𝓝 hf hs (mem_cechCc_iff.mp hx I)
  choose y hy hyx using this
  exact ⟨y, mem_cechCc_iff.mpr hy, funext hyx⟩

theorem cechMap_mem_cechBc {𝓜 : (K → ℤ) → Submodule S M} {𝓝 : (K → ℤ) → Submodule S N}
    {f : M →ₗ[MRingOver S ι] N} (hf : KH.IsMGradedMap S ι 𝓜 𝓝 f) {c : K → ℤ} :
    ∀ {n : ℕ} {z : KH.CechC S ι M n}, z ∈ KH.cechBc ι 𝓜 c n → KH.cechMap S ι f n z ∈ KH.cechBc ι 𝓝 c n
  | 0, z, hz => by
    have hz0 : z = 0 := (Submodule.mem_bot S).mp hz
    rw [hz0, map_zero]
    exact zero_mem _
  | n + 1, _, ⟨y, hy, rfl⟩ =>
    ⟨KH.cechMap S ι f n y, (KHCechMapDeg.full S K ι M N 𝓜 𝓝 f c n hf).1 y hy, KHTheoremS.cechD_cechMap f n y⟩

theorem cechBc_le_cechZc (hSq : KH.CechDSqStatement) (hDeg : KH.CechDDegStatement)
    (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) : ∀ n : ℕ, KH.cechBc ι 𝓜 c n ≤ KH.cechZc ι 𝓜 c n
  | 0 => bot_le
  | n + 1 => by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨hDeg S K ι M 𝓜 c n y hy, LinearMap.mem_ker.mpr ?_⟩
    exact LinearMap.congr_fun (hSq S K ι M n) y

def zMap {𝓜 : (K → ℤ) → Submodule S M} {𝓝 : (K → ℤ) → Submodule S N} (f : M →ₗ[MRingOver S ι] N)
    (hf : KH.IsMGradedMap S ι 𝓜 𝓝 f) (c : K → ℤ) (n : ℕ) :
    KH.cechZc ι 𝓜 c n →ₗ[S] KH.cechZc ι 𝓝 c n :=
  LinearMap.codRestrict (KH.cechZc ι 𝓝 c n)
    (((KH.cechMap S ι f n).restrictScalars S).comp (KH.cechZc ι 𝓜 c n).subtype)
    (fun z => KHTheoremS.cechMap_mem_cechZc hf z.2)

def hMap {𝓜 : (K → ℤ) → Submodule S M} {𝓝 : (K → ℤ) → Submodule S N} (f : M →ₗ[MRingOver S ι] N)
    (hf : KH.IsMGradedMap S ι 𝓜 𝓝 f) (c : K → ℤ) (n : ℕ) :
    KH.cechHc ι 𝓜 c n →ₗ[S] KH.cechHc ι 𝓝 c n :=
  Submodule.mapQ _ _ (zMap f hf c n) (fun _ hz => cechMap_mem_cechBc hf hz)

theorem hMap_mk {𝓜 : (K → ℤ) → Submodule S M} {𝓝 : (K → ℤ) → Submodule S N} (f : M →ₗ[MRingOver S ι] N)
    (hf : KH.IsMGradedMap S ι 𝓜 𝓝 f) (c : K → ℤ) (n : ℕ) (z : KH.cechZc ι 𝓜 c n) :
    hMap f hf c n (Submodule.Quotient.mk z) = Submodule.Quotient.mk (zMap f hf c n z) := rfl

end General

section SES

variable {M' M M'' : Type} [AddCommGroup M'] [Module (MRingOver S ι) M'] [Module S M']
  [IsScalarTower S (MRingOver S ι) M'] [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] [AddCommGroup M''] [Module (MRingOver S ι) M''] [Module S M'']
  [IsScalarTower S (MRingOver S ι) M'']
  {𝓜' : (K → ℤ) → Submodule S M'} {𝓜 : (K → ℤ) → Submodule S M} {𝓜'' : (K → ℤ) → Submodule S M''}
  {g : M' →ₗ[MRingOver S ι] M} {h : M →ₗ[MRingOver S ι] M''}

theorem cechMap_comp_eq_zero (hex : LinearMap.range g = LinearMap.ker h) (n : ℕ) (x : KH.CechC S ι M' n) :
    KH.cechMap S ι h n (KH.cechMap S ι g n x) = 0 := by
  funext I
  rw [KHTheoremS.cechMap_apply, KHTheoremS.cechMap_apply, Pi.zero_apply]
  induction x I using LocalizedModule.induction_on with
  | h m t =>
    have hgm : h (g m) = 0 := by
      rw [← LinearMap.mem_ker, ← hex]
      exact LinearMap.mem_range_self g m
    rw [KHTheoremS.lmap_mk, KHTheoremS.lmap_mk, hgm, LocalizedModule.zero_mk]

theorem locPart_exact (h𝓜' : KH.IsMGraded S ι 𝓜') (h𝓜 : KH.IsMGraded S ι 𝓜)
    (hg : KH.IsMGradedMap S ι 𝓜' 𝓜 g) (hinj : Function.Injective g)
    (hex : LinearMap.range g = LinearMap.ker h) {I : ∀ k, Finset (ι k)} {c : K → ℤ}
    {x : LocalizedModule (KH.cellMon S I) M} (hx : x ∈ KH.locPart ι 𝓜 (KH.cellMon S I) c)
    (h0 : KHTheoremS.lmap _ h x = 0) :
    ∃ y ∈ KH.locPart ι 𝓜' (KH.cellMon S I) c, KHTheoremS.lmap _ g y = x := by
  obtain ⟨m, t, a, ht, hm, rfl⟩ := GenSESStep.locPart_normal h𝓜 hx
  rw [KHTheoremS.lmap_mk, ← LocalizedModule.zero_mk t, LocalizedModule.mk_eq] at h0
  obtain ⟨u, hu⟩ := h0
  set v : KH.cellMon S I := u * t with hv_def
  have hv : h ((v : MRingOver S ι) • m) = 0 := by
    rw [map_smul]
    simpa [v, Submonoid.smul_def, mul_smul] using hu
  obtain ⟨e, he⟩ := GenSESStep.cellMon_homog v.2
  have hvm : (v : MRingOver S ι) • m ∈ 𝓜 ((c + fun k => (a k : ℤ)) + fun k => (e k : ℤ)) :=
    h𝓜.2 e _ _ m he hm
  obtain ⟨m', hm'⟩ : (v : MRingOver S ι) • m ∈ LinearMap.range g := by
    rw [hex]
    exact LinearMap.mem_ker.mpr hv
  have hm'deg := GenSESStep.mem_of_map_mem h𝓜' h𝓜 hg hinj (hm' ▸ hvm)
  refine ⟨LocalizedModule.mk m' (v * t), ?_, ?_⟩
  · refine GenSESStep.mk_mem_locPart m' (v * t) (e + a) (GenSESStep.isMultiHomog_mul he ht) ?_
    convert hm'deg using 2
    funext k
    simp only [Pi.add_apply, Nat.cast_add]
    ring
  · rw [KHTheoremS.lmap_mk, hm', ← Submonoid.smul_def, LocalizedModule.mk_cancel_common_left]

theorem cechMap_exact (h𝓜' : KH.IsMGraded S ι 𝓜') (h𝓜 : KH.IsMGraded S ι 𝓜)
    (hg : KH.IsMGradedMap S ι 𝓜' 𝓜 g) (hinj : Function.Injective g)
    (hex : LinearMap.range g = LinearMap.ker h) {c : K → ℤ} {n : ℕ} {x : KH.CechC S ι M n}
    (hx : x ∈ KH.cechCc ι 𝓜 c n) (h0 : KH.cechMap S ι h n x = 0) :
    ∃ y ∈ KH.cechCc ι 𝓜' c n, KH.cechMap S ι g n y = x := by
  have := fun I : KH.Cell K ι n =>
    locPart_exact h𝓜' h𝓜 hg hinj hex (mem_cechCc_iff.mp hx I) (congrFun h0 I)
  choose y hy hyx using this
  exact ⟨y, mem_cechCc_iff.mpr hy, funext hyx⟩

theorem cechBc_lift (h𝓜 : KH.IsMGraded S ι 𝓜) (h𝓜'' : KH.IsMGraded S ι 𝓜'')
    (hh : KH.IsMGradedMap S ι 𝓜 𝓜'' h) (hsurj : Function.Surjective h) {c : K → ℤ} :
    ∀ {n : ℕ} {x : KH.CechC S ι M'' n}, x ∈ KH.cechBc ι 𝓜'' c n →
      ∃ b ∈ KH.cechBc ι 𝓜 c n, KH.cechMap S ι h n b = x
  | 0, x, hx => by
    have hx0 : x = 0 := (Submodule.mem_bot S).mp hx
    exact ⟨0, zero_mem _, by rw [hx0, map_zero]⟩
  | n + 1, _, ⟨y, hy, rfl⟩ => by
    obtain ⟨z, hz, rfl⟩ := cechMap_lift h𝓜 h𝓜'' hh hsurj hy
    exact ⟨KH.cechD S ι M n z, ⟨z, hz, rfl⟩, (KHTheoremS.cechD_cechMap h n z).symm⟩

theorem exists_sub_mem_cechBc (hSq : KH.CechDSqStatement) (hDeg : KH.CechDDegStatement)
    (h𝓜' : KH.IsMGraded S ι 𝓜') (h𝓜 : KH.IsMGraded S ι 𝓜) (h𝓜'' : KH.IsMGraded S ι 𝓜'')
    (hg : KH.IsMGradedMap S ι 𝓜' 𝓜 g) (hh : KH.IsMGradedMap S ι 𝓜 𝓜'' h) (hinj : Function.Injective g)
    (hsurj : Function.Surjective h) (hex : LinearMap.range g = LinearMap.ker h) {c : K → ℤ} {n : ℕ}
    {z : KH.CechC S ι M n} (hz : z ∈ KH.cechZc ι 𝓜 c n) (hzb : KH.cechMap S ι h n z ∈ KH.cechBc ι 𝓜'' c n) :
    ∃ z' ∈ KH.cechZc ι 𝓜' c n, z - KH.cechMap S ι g n z' ∈ KH.cechBc ι 𝓜 c n := by
  obtain ⟨hzC, hzD⟩ := hz
  obtain ⟨b, hb, hbz⟩ := cechBc_lift h𝓜 h𝓜'' hh hsurj hzb
  obtain ⟨hbC, hbD⟩ := cechBc_le_cechZc hSq hDeg 𝓜 c n hb
  obtain ⟨w, hw, hwz⟩ := cechMap_exact h𝓜' h𝓜 hg hinj hex (x := z - b) (sub_mem hzC hbC)
    (by rw [map_sub, hbz, sub_self])
  have hDz : KH.cechD S ι M n z = 0 := hzD
  have hDb : KH.cechD S ι M n b = 0 := hbD
  refine ⟨w, ⟨hw, LinearMap.mem_ker.mpr (cechMap_injective hinj (n + 1) ?_)⟩, ?_⟩
  · rw [← KHTheoremS.cechD_cechMap, hwz, map_sub, hDz, hDb, sub_zero, map_zero]
  · rw [hwz, sub_sub_cancel]
    exact hb

theorem lift_cocycle (hSq : KH.CechDSqStatement) (hDeg : KH.CechDDegStatement)
    (h𝓜' : KH.IsMGraded S ι 𝓜') (h𝓜 : KH.IsMGraded S ι 𝓜) (h𝓜'' : KH.IsMGraded S ι 𝓜'')
    (hg : KH.IsMGradedMap S ι 𝓜' 𝓜 g) (hh : KH.IsMGradedMap S ι 𝓜 𝓜'' h) (hinj : Function.Injective g)
    (hsurj : Function.Surjective h) (hex : LinearMap.range g = LinearMap.ker h) {c : K → ℤ} {n : ℕ}
    {z'' : KH.CechC S ι M'' n} (hz'' : z'' ∈ KH.cechZc ι 𝓜'' c n) :
    ∃ y ∈ KH.cechCc ι 𝓜 c n, ∃ w ∈ KH.cechZc ι 𝓜' c (n + 1),
      KH.cechD S ι M n y = KH.cechMap S ι g (n + 1) w ∧ KH.cechMap S ι h n y = z'' := by
  obtain ⟨hzC, hzD⟩ := hz''
  obtain ⟨y, hy, rfl⟩ := cechMap_lift h𝓜 h𝓜'' hh hsurj hzC
  have hDy := hDeg S K ι M 𝓜 c n y hy
  obtain ⟨w, hw, hwy⟩ := cechMap_exact h𝓜' h𝓜 hg hinj hex hDy
    (by rw [← KHTheoremS.cechD_cechMap]; exact hzD)
  refine ⟨y, hy, w, ⟨hw, LinearMap.mem_ker.mpr (cechMap_injective hinj (n + 1 + 1) ?_)⟩, hwy.symm, rfl⟩
  rw [← KHTheoremS.cechD_cechMap, hwy, map_zero]
  exact LinearMap.congr_fun (hSq S K ι M n) y

theorem adjust (hg : KH.IsMGradedMap S ι 𝓜' 𝓜 g)
    (hex : LinearMap.range g = LinearMap.ker h) {c : K → ℤ} {n : ℕ} {y : KH.CechC S ι M n}
    (hy : y ∈ KH.cechCc ι 𝓜 c n) {w : KH.CechC S ι M' (n + 1)}
    (hyw : KH.cechD S ι M n y = KH.cechMap S ι g (n + 1) w) {v : KH.CechC S ι M' n}
    (hv : v ∈ KH.cechCc ι 𝓜' c n) (hvw : KH.cechD S ι M' n v = w) :
    y - KH.cechMap S ι g n v ∈ KH.cechZc ι 𝓜 c n ∧
      KH.cechMap S ι h n (y - KH.cechMap S ι g n v) = KH.cechMap S ι h n y := by
  refine ⟨⟨sub_mem hy ((KHCechMapDeg.full S K ι M' M 𝓜' 𝓜 g c n hg).1 v hv), LinearMap.mem_ker.mpr ?_⟩, ?_⟩
  · rw [map_sub, KHTheoremS.cechD_cechMap, hvw, hyw, sub_self]
  · rw [map_sub, cechMap_comp_eq_zero hex, sub_zero]

theorem exists_cocycle_of_vanish (hSq : KH.CechDSqStatement) (hDeg : KH.CechDDegStatement)
    (h𝓜' : KH.IsMGraded S ι 𝓜') (h𝓜 : KH.IsMGraded S ι 𝓜) (h𝓜'' : KH.IsMGraded S ι 𝓜'')
    (hg : KH.IsMGradedMap S ι 𝓜' 𝓜 g) (hh : KH.IsMGradedMap S ι 𝓜 𝓜'' h) (hinj : Function.Injective g)
    (hsurj : Function.Surjective h) (hex : LinearMap.range g = LinearMap.ker h) {c : K → ℤ} {n : ℕ}
    (hZ' : KH.cechZc ι 𝓜' c (n + 1) ≤ KH.cechBc ι 𝓜' c (n + 1))
    {z'' : KH.CechC S ι M'' n} (hz'' : z'' ∈ KH.cechZc ι 𝓜'' c n) :
    ∃ z ∈ KH.cechZc ι 𝓜 c n, KH.cechMap S ι h n z = z'' := by
  obtain ⟨y, hy, w, hw, hyw, rfl⟩ := lift_cocycle hSq hDeg h𝓜' h𝓜 h𝓜'' hg hh hinj hsurj hex hz''
  obtain ⟨v, hv, hvw⟩ := hZ' hw
  obtain ⟨hz, he⟩ := adjust hg hex hy hyw hv hvw
  exact ⟨_, hz, he⟩

theorem exists_preimage_cocycle (h𝓜' : KH.IsMGraded S ι 𝓜') (h𝓜 : KH.IsMGraded S ι 𝓜)
    (hg : KH.IsMGradedMap S ι 𝓜' 𝓜 g) (hinj : Function.Injective g)
    (hex : LinearMap.range g = LinearMap.ker h) {c : K → ℤ} {n : ℕ} {z : KH.CechC S ι M n}
    (hz : z ∈ KH.cechZc ι 𝓜 c n) (h0 : KH.cechMap S ι h n z = 0) :
    ∃ z' ∈ KH.cechZc ι 𝓜' c n, KH.cechMap S ι g n z' = z := by
  obtain ⟨hzC, hzD⟩ := hz
  obtain ⟨w, hw, rfl⟩ := cechMap_exact h𝓜' h𝓜 hg hinj hex hzC h0
  refine ⟨w, ⟨hw, LinearMap.mem_ker.mpr (cechMap_injective hinj (n + 1) ?_)⟩, rfl⟩
  rw [← KHTheoremS.cechD_cechMap, map_zero]
  exact hzD

theorem finite_middle (hSq : KH.CechDSqStatement) (hDeg : KH.CechDDegStatement)
    (h𝓜' : KH.IsMGraded S ι 𝓜') (h𝓜 : KH.IsMGraded S ι 𝓜) (h𝓜'' : KH.IsMGraded S ι 𝓜'')
    (hg : KH.IsMGradedMap S ι 𝓜' 𝓜 g) (hh : KH.IsMGradedMap S ι 𝓜 𝓜'' h) (hinj : Function.Injective g)
    (hsurj : Function.Surjective h) (hex : LinearMap.range g = LinearMap.ker h) (hS : IsNoetherianRing S)
    (c : K → ℤ) (n : ℕ) (hF' : Module.Finite S (KH.cechHc ι 𝓜' c n))
    (hF'' : Module.Finite S (KH.cechHc ι 𝓜'' c n)) : Module.Finite S (KH.cechHc ι 𝓜 c n) := by
  refine finite_of_ker_le LinearMap.id Function.surjective_id (hMap h hh c n)
    (LinearMap.range (hMap g hg c n)) ?_ ?_
  · rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  · intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hMap_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨z', hz', hzz⟩ :=
      exists_sub_mem_cechBc hSq hDeg h𝓜' h𝓜 h𝓜'' hg hh hinj hsurj hex z.2 hx
    refine ⟨Submodule.Quotient.mk ⟨z', hz'⟩, ?_⟩
    rw [hMap_mk, LinearMap.id_apply, Submodule.Quotient.eq]
    have := neg_mem hzz
    rw [neg_sub] at this
    exact this

def pairs (g : M' →ₗ[MRingOver S ι] M) (𝓜 : (K → ℤ) → Submodule S M) (𝓜' : (K → ℤ) → Submodule S M')
    (c : K → ℤ) (n : ℕ) : Submodule S (KH.CechC S ι M n × KH.CechC S ι M' (n + 1)) where
  carrier := {p | p.1 ∈ KH.cechCc ι 𝓜 c n ∧ p.2 ∈ KH.cechZc ι 𝓜' c (n + 1) ∧
    KH.cechD S ι M n p.1 = KH.cechMap S ι g (n + 1) p.2}
  add_mem' := fun {p q} hp hq => ⟨add_mem hp.1 hq.1, add_mem hp.2.1 hq.2.1, by
    rw [Prod.fst_add, Prod.snd_add, map_add, map_add, hp.2.2, hq.2.2]⟩
  zero_mem' := ⟨zero_mem _, zero_mem _, by rw [Prod.fst_zero, Prod.snd_zero, map_zero, map_zero]⟩
  smul_mem' := fun s p hp => ⟨Submodule.smul_mem _ s hp.1, Submodule.smul_mem _ s hp.2.1, by
    rw [Prod.smul_fst, Prod.smul_snd, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, hp.2.2]⟩

theorem finite_right (hSq : KH.CechDSqStatement) (hDeg : KH.CechDDegStatement)
    (h𝓜' : KH.IsMGraded S ι 𝓜') (h𝓜 : KH.IsMGraded S ι 𝓜) (h𝓜'' : KH.IsMGraded S ι 𝓜'')
    (hg : KH.IsMGradedMap S ι 𝓜' 𝓜 g) (hh : KH.IsMGradedMap S ι 𝓜 𝓜'' h) (hinj : Function.Injective g)
    (hsurj : Function.Surjective h) (hex : LinearMap.range g = LinearMap.ker h) (hS : IsNoetherianRing S)
    (c : K → ℤ) (n : ℕ) (hF : Module.Finite S (KH.cechHc ι 𝓜 c n))
    (hF' : Module.Finite S (KH.cechHc ι 𝓜' c (n + 1))) : Module.Finite S (KH.cechHc ι 𝓜'' c n) := by
  have hπ : ∀ p : pairs g 𝓜 𝓜' c n, KH.cechMap S ι h n p.1.1 ∈ KH.cechZc ι 𝓜'' c n := fun p =>
    ⟨(KHCechMapDeg.full S K ι M M'' 𝓜 𝓜'' h c n hh).1 _ p.2.1, LinearMap.mem_ker.mpr (by
      rw [KHTheoremS.cechD_cechMap, p.2.2.2, cechMap_comp_eq_zero hex])⟩
  refine finite_of_ker_le
    (Submodule.mkQ ((KH.cechBc ι 𝓜'' c n).comap (KH.cechZc ι 𝓜'' c n).subtype) ∘ₗ
      LinearMap.codRestrict (KH.cechZc ι 𝓜'' c n)
        (((KH.cechMap S ι h n).restrictScalars S) ∘ₗ LinearMap.fst S _ _ ∘ₗ (pairs g 𝓜 𝓜' c n).subtype) hπ)
    ?_
    (Submodule.mkQ ((KH.cechBc ι 𝓜' c (n + 1)).comap (KH.cechZc ι 𝓜' c (n + 1)).subtype) ∘ₗ
      LinearMap.codRestrict (KH.cechZc ι 𝓜' c (n + 1))
        (LinearMap.snd S _ _ ∘ₗ (pairs g 𝓜 𝓜' c n).subtype) (fun p => p.2.2.1))
    (LinearMap.range (hMap h hh c n)) ?_ ?_
  · intro x
    obtain ⟨z'', rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, hy, w, hw, hyw, hyz⟩ := lift_cocycle hSq hDeg h𝓜' h𝓜 h𝓜'' hg hh hinj hsurj hex z''.2
    refine ⟨⟨(y, w), hy, hw, hyw⟩, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply]
    congr 1
    exact Subtype.ext hyz
  · rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  · intro p hp
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hp
    obtain ⟨v, hv, hvw⟩ := (hp : p.1.2 ∈ KH.cechBc ι 𝓜' c (n + 1))
    obtain ⟨hz, he⟩ := adjust hg hex p.2.1 p.2.2.2 hv hvw
    refine ⟨Submodule.Quotient.mk ⟨_, hz⟩, ?_⟩
    rw [hMap_mk, LinearMap.comp_apply, Submodule.mkQ_apply]
    congr 1
    exact Subtype.ext he

end SES

end KHCechSES

theorem KHCechSES.proof (hSq : KH.CechDSqStatement) (hDeg : KH.CechDDegStatement) : KH.CechSESStatement := by
  intro S _ K _ _ ι _ _ M' _ _ _ _ M _ _ _ _ M'' _ _ _ _ 𝓜' 𝓜 𝓜'' g h h𝓜' h𝓜 h𝓜'' hg hh hinj hsurj hex c n
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun hS h1 h2 => ?_, fun hS h1 h2 => ?_, fun h1 => ?_,
    fun z hz h0 => ?_⟩
  · rw [H1VanishingDevissage.cechHc_subsingleton_iff] at h1 h2 ⊢
    intro z hz
    obtain ⟨z', hz', hzz⟩ := KHCechSES.exists_sub_mem_cechBc hSq hDeg h𝓜' h𝓜 h𝓜'' hg hh hinj hsurj hex hz
      (h2 (KHTheoremS.cechMap_mem_cechZc hh hz))
    have := add_mem hzz (KHCechSES.cechMap_mem_cechBc hg (h1 hz'))
    rwa [sub_add_cancel] at this
  · rw [H1VanishingDevissage.cechHc_subsingleton_iff] at h1 h2 ⊢
    intro z'' hz''
    obtain ⟨z, hz, rfl⟩ :=
      KHCechSES.exists_cocycle_of_vanish hSq hDeg h𝓜' h𝓜 h𝓜'' hg hh hinj hsurj hex h2 hz''
    exact KHCechSES.cechMap_mem_cechBc hh (h1 hz)
  · exact KHCechSES.finite_middle hSq hDeg h𝓜' h𝓜 h𝓜'' hg hh hinj hsurj hex hS c n h1 h2
  · exact KHCechSES.finite_right hSq hDeg h𝓜' h𝓜 h𝓜'' hg hh hinj hsurj hex hS c n h1 h2
  · rw [H1VanishingDevissage.cechHc_subsingleton_iff] at h1
    intro z'' hz''
    exact KHCechSES.exists_cocycle_of_vanish hSq hDeg h𝓜' h𝓜 h𝓜'' hg hh hinj hsurj hex h1 hz''
  · exact KHCechSES.exists_preimage_cocycle h𝓜' h𝓜 hg hinj hex hz h0

end

end GroundTheory.Heights₂.Heights.Kleiman
