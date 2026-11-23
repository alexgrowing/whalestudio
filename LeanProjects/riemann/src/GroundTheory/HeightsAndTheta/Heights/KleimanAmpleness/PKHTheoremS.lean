import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHTheoremSAux
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace KHTheoremS

def FinVanAt (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (n : ℕ) : Prop :=
  ∀ (N : Type) [AddCommGroup N] [Module (MRingOver S ι) N] [Module S N] [IsScalarTower S (MRingOver S ι) N]
    (𝓝 : (K → ℤ) → Submodule S N), Module.Finite (MRingOver S ι) N → KH.IsMGraded S ι 𝓝 →
    (∀ c : K → ℤ, Module.Finite S (KH.cechHc ι 𝓝 c n)) ∧
    (1 ≤ n → ∃ c₀ : ℤ, ∀ c : K → ℤ, (∀ k, c₀ ≤ c k) → Subsingleton (KH.cechHc ι 𝓝 c n))

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem finite_of_subsingleton (X : Type) [AddCommGroup X] [Module S X] (h : Subsingleton X) :
    Module.Finite S X :=
  Module.finite_def.2 (by rw [Subsingleton.elim (⊤ : Submodule S X) ⊥]; exact Submodule.fg_bot)

theorem add_nonneg_of_le (e c : K → ℤ) (h : ∀ k, ∑ l, |e l| ≤ c k) (k : K) : 0 ≤ c k + e k := by
  have h1 : |e k| ≤ ∑ l, |e l| := Finset.single_le_sum (fun l _ => abs_nonneg (e l)) (Finset.mem_univ k)
  have h2 := neg_abs_le (e k)
  have h3 := h k
  linarith

theorem finVanAt_top (n : ℕ) (hn : ∑ k, (Fintype.card (ι k) - 1) < n) : FinVanAt S K ι n := by
  intro N _ _ _ _ 𝓝 _ _
  have h := fun c => KHCechTop.full S K ι N 𝓝 c n hn
  exact ⟨fun c => finite_of_subsingleton _ (h c), fun _ => ⟨0, fun c _ => h c⟩⟩

theorem finVanAt_step (hFree : KH.TheoremSFreeStatement) (hSES : KH.CechSESStatement)
    (hPF : KH.PrimeFiltStatement) (hS : IsNoetherianRing S) (n : ℕ) (ih : FinVanAt S K ι (n + 1)) :
    FinVanAt S K ι n := by
  intro N _ _ _ _ 𝓝 hfin hgr
  refine devissage hPF hS (fun (N : Type) [AddCommGroup N] [Module (MRingOver S ι) N] [Module S N] [IsScalarTower S (MRingOver S ι) N] (𝓝 : (K → ℤ) → Submodule S N) => (∀ c : K → ℤ, Module.Finite S (KH.cechHc ι 𝓝 c n)) ∧
    (1 ≤ n → ∃ c₀ : ℤ, ∀ c : K → ℤ, (∀ k, c₀ ≤ c k) → Subsingleton (KH.cechHc ι 𝓝 c n)))
    ⟨fun c => finite_of_subsingleton _ (cechHc_punit c n), fun _ => ⟨0, fun c _ => cechHc_punit c n⟩⟩
    ?_ ?_ N 𝓝 hfin hgr
  · intro M' _ _ _ _ M _ _ _ _ M'' _ _ _ _ 𝓜' 𝓜 𝓜'' g h hg' hg hg'' hgg hhg hinj hsurj hex ⟨f', v'⟩ ⟨f'', v''⟩
    have hs := hSES S K ι M' M M'' 𝓜' 𝓜 𝓜'' g h hg' hg hg'' hgg hhg hinj hsurj hex
    refine ⟨fun c => (hs c n).2.2.1 hS (f' c) (f'' c), fun hn => ?_⟩
    obtain ⟨c₁, h₁⟩ := v' hn
    obtain ⟨c₂, h₂⟩ := v'' hn
    exact ⟨max c₁ c₂, fun c hc => (hs c n).1 (h₁ c fun k => le_of_max_le_left (hc k))
      (h₂ c fun k => le_of_max_le_right (hc k))⟩
  · intro 𝔭 _ hhom e
    obtain ⟨hgN, hgF, hgQ, hgi, hgq, hinj, hsurj, hex⟩ := quotSES 𝔭 hhom e
    have hs := hSES S K ι (idealSub 𝔭) (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) (MRingOver S ι ⧸ 𝔭)
      _ (fun d => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (d + e)) (fun d => KH.quotPart S 𝔭 (d + e))
      (idealSub 𝔭).subtype (quotMap 𝔭) hgN hgF hgQ hgi hgq hinj hsurj hex
    obtain ⟨fN, vN⟩ := ih (idealSub 𝔭) _ (idealSub_finite hS 𝔭) hgN
    refine ⟨fun c => (hs c n).2.2.2.1 hS ((hFree S K ι e).1 c n) (fN c), fun hn => ?_⟩
    obtain ⟨c₁, h₁⟩ := vN (Nat.le_succ_of_le hn)
    refine ⟨max c₁ (∑ l, |e l|), fun c hc => (hs c n).2.1 ?_ (h₁ c fun k => le_of_max_le_left (hc k))⟩
    exact (hFree S K ι e).2.1 c n hn
      (add_nonneg_of_le e c fun k => le_of_max_le_right (hc k))

theorem finVanAt_all (hFree : KH.TheoremSFreeStatement) (hSES : KH.CechSESStatement)
    (hPF : KH.PrimeFiltStatement) (hS : IsNoetherianRing S) (n : ℕ) : FinVanAt S K ι n := by
  have key : ∀ t n : ℕ, ∑ k, (Fintype.card (ι k) - 1) < n + t → FinVanAt S K ι n := by
    intro t
    induction t with
    | zero => exact fun n h => finVanAt_top n h
    | succ t ih => exact fun n h => finVanAt_step hFree hSES hPF hS n (ih (n + 1) (by omega))
  exact key (∑ k, (Fintype.card (ι k) - 1) + 1) n (by omega)

theorem onto (hFree : KH.TheoremSFreeStatement) (hSES : KH.CechSESStatement)
    (hPF : KH.PrimeFiltStatement) (hS : IsNoetherianRing S)
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (hfin : Module.Finite (MRingOver S ι) M) (hgr : KH.IsMGraded S ι 𝓜) :
    ∃ c₀ : ℤ, ∀ c : K → ℤ, (∀ k, c₀ ≤ c k) → ∀ z ∈ KH.cechZc ι 𝓜 c 0,
      ∃ m ∈ 𝓜 c, ∀ I, z I = LocalizedModule.mk m 1 := by
  refine devissage hPF hS (fun (N : Type) [AddCommGroup N] [Module (MRingOver S ι) N] [Module S N] [IsScalarTower S (MRingOver S ι) N] (𝓝 : (K → ℤ) → Submodule S N) => ∃ c₀ : ℤ, ∀ c : K → ℤ, (∀ k, c₀ ≤ c k) →
    ∀ z ∈ KH.cechZc ι 𝓝 c 0, ∃ m ∈ 𝓝 c, ∀ I, z I = LocalizedModule.mk m 1)
    ⟨0, fun _ _ z _ => ⟨0, Submodule.zero_mem _, fun _ => Subsingleton.elim (α := LocalizedModule _ PUnit) _ _⟩⟩
    ?_ ?_ M 𝓜 hfin hgr
  · intro M' _ _ _ _ M _ _ _ _ M'' _ _ _ _ 𝓜' 𝓜 𝓜'' g h hg' hg hg'' hgg hhg hinj hsurj hex ⟨a, ha⟩ ⟨b, hb⟩
    have hs := hSES S K ι M' M M'' 𝓜' 𝓜 𝓜'' g h hg' hg hg'' hgg hhg hinj hsurj hex
    refine ⟨max a b, fun c hc z hz => ?_⟩
    obtain ⟨m'', hm'', hz''⟩ := hb c (fun k => le_of_max_le_right (hc k)) _ (cechMap_mem_cechZc hhg hz)
    obtain ⟨m, hm, rfl⟩ := exists_mem_of_surjective hg hg'' hhg hsurj hm''
    have hw : z - (fun _ => LocalizedModule.mk m 1) ∈ KH.cechZc ι 𝓜 c 0 := sub_mem hz (const_mem_cechZc hm)
    have hw0 : KH.cechMap S ι h 0 (z - fun _ => LocalizedModule.mk m 1) = 0 := by
      funext I
      rw [map_sub, Pi.sub_apply, hz'' I]
      show LocalizedModule.mk (h m) 1 - lmap (KH.cellMon S I.1) h (LocalizedModule.mk m 1) = 0
      rw [lmap_mk, sub_self]
    obtain ⟨z', hz', hgz'⟩ := (hs c 0).2.2.2.2.2 _ hw hw0
    obtain ⟨m', hm', hz'I⟩ := ha c (fun k => le_of_max_le_left (hc k)) z' hz'
    refine ⟨g m' + m, add_mem (hgg c m' hm') hm, fun I => ?_⟩
    have e1 : z I - LocalizedModule.mk m 1 = LocalizedModule.mk (g m') 1 := by
      have := congrFun hgz' I
      rw [Pi.sub_apply] at this
      rw [← this]
      show lmap (KH.cellMon S I.1) g (z' I) = _
      rw [hz'I I, lmap_mk]
    calc z I = (z I - LocalizedModule.mk m 1) + LocalizedModule.mk m 1 := (sub_add_cancel _ _).symm
      _ = LocalizedModule.mk (g m') 1 + LocalizedModule.mk m 1 := by rw [e1]
      _ = LocalizedModule.mk (g m' + m) 1 := by rw [LocalizedModule.mk_add_mk, one_smul, one_smul, mul_one]
  · intro 𝔭 _ hhom e
    obtain ⟨hgN, hgF, hgQ, hgi, hgq, hinj, hsurj, hex⟩ := quotSES 𝔭 hhom e
    have hs := hSES S K ι (idealSub 𝔭) (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) (MRingOver S ι ⧸ 𝔭)
      _ (fun d => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (d + e)) (fun d => KH.quotPart S 𝔭 (d + e))
      (idealSub 𝔭).subtype (quotMap 𝔭) hgN hgF hgQ hgi hgq hinj hsurj hex
    obtain ⟨c₁, h₁⟩ := (finVanAt_all hFree hSES hPF hS 1 (idealSub 𝔭) _ (idealSub_finite hS 𝔭) hgN).2 le_rfl
    refine ⟨max c₁ (∑ l, |e l|), fun c hc z hz => ?_⟩
    obtain ⟨zF, hzF, rfl⟩ := (hs c 0).2.2.2.2.1 (h₁ c fun k => le_of_max_le_left (hc k)) z hz
    obtain ⟨f, hf, hfI⟩ := (hFree S K ι e).2.2 c (add_nonneg_of_le e c fun k => le_of_max_le_right (hc k)) zF hzF
    exact ⟨quotMap 𝔭 f, hgq c f hf, fun I => by
      show lmap (KH.cellMon S I.1) (quotMap 𝔭) (zF I) = _
      rw [hfI I, lmap_mk]⟩

end KHTheoremS

theorem KHTheoremS.proof (hFree : KH.TheoremSFreeStatement) (hSES : KH.CechSESStatement)
    (hPF : KH.PrimeFiltStatement) : KH.TheoremSStatement := by
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 hS hfin hgr
  have hFV := fun n => KHTheoremS.finVanAt_all (ι := ι) hFree hSES hPF hS n M 𝓜 hfin hgr
  obtain ⟨c₃, h₃⟩ := KHTheoremS.onto hFree hSES hPF hS M 𝓜 hfin hgr
  refine ⟨fun c n => (hFV n).1 c, ?_, ⟨c₃, h₃⟩, ?_⟩
  ·
    have hb : ∀ B : ℕ, ∃ c₀ : ℤ, ∀ (c : K → ℤ) (n : ℕ), 1 ≤ n → n ≤ B → (∀ k, c₀ ≤ c k) →
        Subsingleton (KH.cechHc ι 𝓜 c n) := by
      intro B
      induction B with
      | zero => exact ⟨0, fun c n h1 h2 _ => absurd h2 (by omega)⟩
      | succ B ih =>
        obtain ⟨c₀, h₀⟩ := ih
        obtain ⟨c₁, h₁⟩ := (hFV (B + 1)).2 (by omega)
        refine ⟨max c₀ c₁, fun c n h1 h2 hc => ?_⟩
        rcases Nat.lt_or_ge n (B + 1) with h | h
        · exact h₀ c n h1 (by omega) fun k => le_of_max_le_left (hc k)
        · rw [show n = B + 1 by omega]
          exact h₁ c fun k => le_of_max_le_right (hc k)
    obtain ⟨c₀, h₀⟩ := hb (∑ k, (Fintype.card (ι k) - 1))
    refine ⟨c₀, fun c n h1 hc => ?_⟩
    rcases Nat.lt_or_ge (∑ k, (Fintype.card (ι k) - 1)) n with h | h
    · exact KHCechTop.full S K ι M 𝓜 c n h
    · exact h₀ c n h1 h hc
  ·

    intro d
    have : IsNoetherianRing (MRingOver S ι) := inferInstance
    let c₁ : ℕ := (c₃ + ∑ k, |d k|).toNat
    let diag : M →ₗ[MRingOver S ι] KH.CechC S ι M 0 :=
      LinearMap.pi fun I => LocalizedModule.mkLinearMap (KH.cellMon S I.1) M
    let Z : ℕ → Submodule S (KH.CechC S ι M 0) := fun c => KH.cechZc ι 𝓜 (d + fun _ => (c : ℤ)) 0
    have hZfg : ∀ c, (Submodule.span (MRingOver S ι) (Z c : Set (KH.CechC S ι M 0))).FG := by
      intro c
      have h0 : (KH.cechBc ι 𝓜 (d + fun _ => (c : ℤ)) 0).comap (Z c).subtype = ⊥ := by
        show (⊥ : Submodule S _).comap (Z c).subtype = ⊥
        rw [Submodule.comap_bot, Submodule.ker_subtype]
      have hfinZ : Module.Finite S (Z c) := by
        have := (hFV 0).1 (d + fun _ => (c : ℤ))
        exact Module.Finite.equiv (Submodule.quotEquivOfEqBot _ h0)
      obtain ⟨s, hs⟩ := Module.Finite.iff_fg.mp hfinZ
      refine ⟨s, ?_⟩
      rw [← hs, Submodule.span_span_of_tower]
    have hle : Submodule.span (MRingOver S ι) (⋃ c : ℕ, (Z c : Set (KH.CechC S ι M 0))) ≤
        (⨆ c : Fin c₁, Submodule.span (MRingOver S ι) (Z c : Set (KH.CechC S ι M 0))) ⊔ LinearMap.range diag := by
      rw [Submodule.span_le]
      intro z hz
      obtain ⟨c, hzc⟩ := Set.mem_iUnion.mp hz
      rcases Nat.lt_or_ge c c₁ with h | h
      · exact Submodule.mem_sup_left (Submodule.mem_iSup_of_mem (⟨c, h⟩ : Fin c₁) (Submodule.subset_span hzc))
      · refine Submodule.mem_sup_right ?_
        have hc : ∀ k, c₃ ≤ d k + (c : ℤ) := by
          intro k
          have h1 : |d k| ≤ ∑ l, |d l| := Finset.single_le_sum (fun l _ => abs_nonneg (d l)) (Finset.mem_univ k)
          have h2 := neg_abs_le (d k)
          have h3 : c₃ + ∑ l, |d l| ≤ (c : ℤ) := by
            have := Int.self_le_toNat (c₃ + ∑ l, |d l|)
            have h4 : ((c₁ : ℕ) : ℤ) ≤ (c : ℤ) := by exact_mod_cast h
            simp only [c₁] at h4
            linarith
          linarith
        obtain ⟨m, -, hm⟩ := h₃ _ (fun k => hc k) z hzc
        exact ⟨m, funext fun I => (hm I).symm⟩
    refine Submodule.FG.of_le (Submodule.FG.sup (Submodule.fg_iSup
      (fun c : Fin c₁ => Submodule.span (MRingOver S ι) (Z c : Set (KH.CechC S ι M 0))) fun c => hZfg c) ?_) hle
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map diag

end

end GroundTheory.Heights₂.Heights.Kleiman
