import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelNonzeroUnit

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelInstances

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}
variable {p : ℕ} [Fact p.Prime] {X : Sys p} {Y : Pend X} {u : D.what₂.Word} {μ : D.what₂.Tup}

theorem smul_one_tup (j : ℕ) (a : X.Lv.comp j) (L0 : (X.Pj j).Tup) : (X.Lv.lev j a).smul 1 L0 = L0 := by
  funext v
  ext z
  simp [Level.smul]

theorem clsBij_of (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) (j : ℕ) (hjm : j ≤ X.mm)
    (hiff : ∀ (a a' : X.Lv.comp j) (L0 L1 : (X.Pj j).Tup), (X.Pj j).IsLatTup L0 → (X.Pj j).IsLatTup L1 →
      (cls j a L0 = cls j a' L1 ↔ a = a' ∧ ∃ γ : (X.Lv.lev j a).Γ, L1 = (X.Lv.lev j a).smul γ L0))
    (hsurj : ∀ x : (D.chTw u μ).cls j, ∃ a L0, (X.Pj j).IsLatTup L0 ∧ cls j a L0 = x) :
    ClsBij (Y := Y) u μ cls j := by
  constructor
  · rintro ⟨⟨a1, L1⟩, m1⟩ ⟨⟨a2, L2⟩, m2⟩ heq
    have hl1 := Y.Rep_lat j _ m1
    have hl2 := Y.Rep_lat j _ m2
    obtain ⟨rfl, γ, hγ⟩ := (hiff a1 a2 L1 L2 hl1 hl2).1 heq
    obtain ⟨L0, _, hu⟩ := Y.Rep_ex j hjm a1 L2 hl2
    have e1 : L1 = L0 := hu L1 ⟨m1, γ, hγ⟩
    have e2 : L2 = L0 := hu L2 ⟨m2, 1, (smul_one_tup j a1 L2).symm⟩
    subst e1
    subst e2
    rfl
  · intro x
    obtain ⟨a, L0, hL, hx⟩ := hsurj x
    obtain ⟨L1, ⟨hmem, γ, hγ⟩, _⟩ := Y.Rep_ex j hjm a L0 hL
    refine ⟨⟨(a, L1), hmem⟩, ?_⟩
    show cls j a L1 = x
    rw [← hx]
    exact (hiff a a L1 L0 (Y.Rep_lat j _ hmem) hL).2 ⟨rfl, γ, hγ⟩

theorem fq_le_span {σ : D.what₂.LL →+* X.G.Kf} (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (j : ℕ)
    (hint : Submodule.span X.G.O (cmp j '' (((ex.tw.fm u μ).lat j).L : Set ((ex.tw.fm u μ).lat j).V)) = X.Lv.Int j) :
    X.FQ j ≤ Submodule.span X.G.Kf (Set.range (cmp j)) := by
  have h1 : X.Lv.Int j ≤ (Submodule.span X.G.Kf (Set.range (cmp j))).restrictScalars X.G.O := by
    rw [← hint]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, _, rfl⟩
    exact Submodule.subset_span ⟨x, rfl⟩
  exact Submodule.span_le.2 fun z hz => h1 hz

theorem cmp_mem_fq {σ : D.what₂.LL →+* X.G.Kf} (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (j : ℕ)
    (hint : Submodule.span X.G.O (cmp j '' (((ex.tw.fm u μ).lat j).L : Set ((ex.tw.fm u μ).lat j).V)) = X.Lv.Int j)
    (y : ((ex.tw.fm u μ).lat j).V) : cmp j y ∈ X.FQ j := by
  have hy : y ∈ Submodule.span D.what₂.LL (((ex.tw.fm u μ).lat j).L : Set ((ex.tw.fm u μ).lat j).V) := by
    rw [((ex.tw.fm u μ).lat_good j).2.2]
    exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem z hz =>
    refine Submodule.subset_span ?_
    change cmp j z ∈ X.Lv.Int j
    rw [← hint]
    exact Submodule.subset_span (Set.mem_image_of_mem _ hz)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul a b _ hb => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hb

theorem admissible_third_chain {σ : D.what₂.LL →+* X.G.Kf} (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (j : ℕ)
    (hint : Submodule.span X.G.O (cmp j '' (((ex.tw.fm u μ).lat j).L : Set ((ex.tw.fm u μ).lat j).V)) = X.Lv.Int j)
    (hint' : Submodule.span X.G.O (cmp (j + 1) '' (((ex.tw.fm u μ).lat (j + 1)).L : Set ((ex.tw.fm u μ).lat (j + 1)).V)) =
      X.Lv.Int (j + 1))
    (hrat : (ex.tw.fm u μ).KRat j)
    (hCh : ∀ (x : ((ex.tw.fm u μ).lat j).V) (y : ((ex.tw.fm u μ).lat (j + 1)).V),
      (ex.tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((ex.tw.fm u μ).emb j x) → X.Kz j (cmp j x) = cmp (j + 1) y)
    (F : X.Fm j) (hF : F ∈ X.FQ j) : X.Kz j F ∈ X.FQ (j + 1) := by
  have hs := fq_le_span cmp j hint hF
  clear hF
  induction hs using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, hy⟩ := hrat x
    rw [hCh x y hy]
    exact cmp_mem_fq cmp (j + 1) hint' y
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul a b _ hb => rw [map_smul]; exact Submodule.smul_mem _ a hb

theorem second_kernel_at_place (t : KerEntTied ex) {σ : D.what₂.LL →+* X.G.Kf} (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j)
    (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (ι : ℂ →+* Y.Kc)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (hj : j < D.R.m)
    (hspan : X.FQ j ≤ Submodule.span X.G.Kf (Set.range (cmp j))) (hrat : (ex.tw.fm u μ).KRat j)
    (hCh : ∀ (x : ((ex.tw.fm u μ).lat j).V) (y : ((ex.tw.fm u μ).lat (j + 1)).V),
      (ex.tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((ex.tw.fm u μ).emb j x) → X.Kz j (cmp j x) = cmp (j + 1) y)
    (hbij : ClsBij (Y := Y) u μ cls j) (hT : TiesAt t u μ cls cmp ι Rd Sr j) : SecondKernelAtLevel X Y j := by
  obtain ⟨hSh, hSt, hRd, hSer, cK, h1, h2, h3, hDel⟩ := hT
  refine ⟨cK, h1, h2, h3, ?_⟩
  intro F hF
  refine body_of_span Y j cK (Set.range (cmp j)) ?_ F (hspan hF)
  rintro _ ⟨x, rfl⟩ c' L' hL
  obtain ⟨y, hy⟩ := hrat x
  have hsum : (D.chTw u μ).K j ((ex.tw.fm u μ).emb j x) =
      ∑ c : (D.chTw u μ).cls j, (((Nat.card ((D.chTw u μ).stab j c) : ℕ) : ℂ))⁻¹ • entRec t ex.tw u μ j c x := by
    have hQ := sharpQ_qOf (hSh x)
    funext c1 y1
    rw [compatible_lift_exists D L hT Gi Gl Kc0 Dx cX ex t u μ j hj _ _ hQ.1 hQ.2 c1 y1]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, entRec]
  rw [hCh x y hy, hRd y c' L' hL, hy, hsum, map_sum]
  rw [← Finset.sum_coe_sort (Y.Rep j)]
  symm
  refine Fintype.sum_bijective _ hbij _ _ fun La => ?_
  rw [map_smulₛₗ, map_inv₀, map_natCast, hSt La.1 La.2, hDel La.1 La.2 x c' L' hL,
    kernel_of_smul p X Y j La.1 (c', L') _ (hSer La.1 La.2 c' L' hL), mul_smul]

end Gen

theorem class_bijection_instance : ClsBijInst := by
  intro D L hT Gi Gl Kc0 Dx cX ex u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y j hj
  exact clsBij_of (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) KA.cls j (hj.trans_eq KA.fl_m.symm)
    (fun a a' L0 L1 h0 h1 => KA.cls_iff j hj a a' L0 L1 h0 h1) (KA.cls_surj j hj)

theorem admissible_third_instance : Adm3bInst := by
  intro D L hT Gi Gl Kc0 Dx cX ex u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om j hj F hF
  have hjm : j < D.R.m := lt_of_lt_of_eq hj KA.fl_m
  exact admissible_third_chain (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) KA.cmp j (KA.cmp_int j hjm.le)
    (KA.cmp_int (j + 1) hjm) (KA.rat j hjm) (fun x y hy => (KA.cmp_K j hjm x y hy).symm) F hF

theorem second_kernel_chain_instance : SecondKernelSingleLevel := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr j hj hTs
  have hsp := fq_le_span (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) KA.cmp j (KA.cmp_int j hj.le)
  have hch : ∀ (x : ((ex.tw.fm u μ).lat j).V) (y : ((ex.tw.fm u μ).lat (j + 1)).V),
      (ex.tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((ex.tw.fm u μ).emb j x) →
      (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Kz j (KA.cmp j x) = KA.cmp (j + 1) y :=
    fun x y hy => (KA.cmp_K j hj x y hy).symm
  have hb : ClsBij (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) (Y := Y) u μ KA.cls j :=
    class_bijection_instance D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y j hj.le
  exact second_kernel_at_place (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) (Y := Y) (σ := ex.cmp.embW u w h) t KA.cls KA.cmp ι Rd Sr
    j hj hsp (KA.rat j hj) hch hb hTs

theorem second_kernel_entry_instance : SecondKernelEntrywise := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr hTs j hj
  exact second_kernel_chain_instance D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr j
    (by omega) (hTs j hj)

end Formalism.L2.KerInert.SecondKernelInstances
