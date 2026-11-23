import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixComponentAtPlaceMemCompletedLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorVacuumEqSmulBasePoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaLocalFactorsStableHeisenbergAwayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanHeisenbergTranslatesOfVacuum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevelStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalSpan

variable {D : D7}

def cutPts (S T : HSp D) (e : AE D) : AddSubgroup (WO S T) where
  carrier := {x | e • x = x}
  zero_mem' := smul_zero e
  add_mem' := fun {x y} hx hy => by
    show e • (x + y) = x + y
    rw [smul_add, show e • x = x from hx, show e • y = y from hy]
  neg_mem' := fun {x} hx => by
    show e • (-x) = -x
    rw [smul_neg, show e • x = x from hx]

theorem idem_fin (D : D7) (v : FinPl D) : idem D (.inl v) * idem D (.inl v) = idem D (.inl v) ∧
    cA D (idem D (.inl v)) = idem D (.inl v) ∧ infPart D (idem D (.inl v)) = 0 := by
  have hss : singleV D.host.F v 1 * singleV D.host.F v 1 = singleV D.host.F v 1 := by
    apply GlobalTheory.LatticeLocal.af_ext D.host.F
    intro w
    rw [map_mul]
    by_cases h : w = v
    · subst h
      simp only [GlobalTheory.LatticeLocal.ev_self, mul_one]
    · simp only [GlobalTheory.LatticeLocal.ev_ne D.host.F h, mul_zero]
  have hrep : idem D (.inl v) = pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    show algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) = _
    rfl
  refine ⟨?_, ?_, ?_⟩
  · calc idem D (.inl v) * idem D (.inl v)
        = idem D (.inl v) * (pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (1 : D.host.E)) := by
          rw [← hrep]
      _ = pairA D.host.F 0 (singleV D.host.F v 1 * singleV D.host.F v 1) ⊗ₜ[D.host.F] (1 : D.host.E) :=
          GlobalTheory.LatticeLocal.idem_inl_mul v _ _
      _ = idem D (.inl v) := by rw [hss, hrep]
  · rw [hrep]
    show (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig) _ = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
  · rw [hrep]
    show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) _ = _
    rw [Algebra.TensorProduct.map_tmul,
      show fstA D.host.F (pairA D.host.F 0 (singleV D.host.F v 1)) = 0 from rfl, TensorProduct.zero_tmul]

theorem symplO_cut {S T : HSp D} {e : AE D} (ce : cA D e = e) {x u : WO S T} (hx : e • x = x) (hu : e • u = 0) :
    symplO S T x u = 0 := by
  rw [← hx, GlobalTheory.SplitScalar.symplO_smul, ce, hu, GlobalTheory.SplitScalar.symplO_zero_right]

private theorem eq_zero_of_eq_neg_AF {F : Type} [Field F] [NumberField F] (a : AF F) (ha : a = -a) : a = 0 := by
  have h2 : (2 : F) • a = 0 := by
    calc (2 : F) • a = a + a := two_smul F a
      _ = a + -a := by rw [← ha]
      _ = 0 := by simp
  calc a = ((1 / 2 : F) * 2) • a := by norm_num
    _ = (1 / 2 : F) • ((2 : F) • a) := mul_smul _ _ _
    _ = 0 := by rw [h2, smul_zero]

private theorem isLatVac_latO_of_local_conditions {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (v : FinPl D) (f : WO S T → ℂ)
    (hoff : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => Sum.inl u ≠ (Sum.inl v : Place D)) f)
    (h2 : ∀ a ∈ latO S T ΛS ΛT (fun u => u = v), idem D (.inl v) • a = a → heisO ψ S T (2 • a) f = f)
    (hs : ∀ e : AE D, IsSplitIdem D e → ∀ a ∈ latO S T ΛS ΛT (fun u => u = v), idem D (.inl v) • a = a →
      IsHalf e a → heisO ψ S T a f = f)
    (P : FinPl D → Prop) : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT P) f := by
  obtain ⟨hii, hci, -⟩ := idem_fin D v
  have split : ∀ u ∈ latO S T ΛS ΛT P,
      wAt (.inl v) u ∈ latO S T ΛS ΛT (fun u => u = v) ∧
      idem D (.inl v) • wAt (.inl v) u = wAt (.inl v) u ∧
      u - wAt (.inl v) u ∈ latO S T ΛS ΛT (fun u => Sum.inl u ≠ (Sum.inl v : Place D)) ∧
      idem D (.inl v) • (u - wAt (.inl v) u) = 0 := by
    intro u hu
    obtain ⟨ha, hb, -⟩ := GlobalTheory.LatticeLocal.wAt_mem_latO D S T ΛS ΛT P u hu (.inl v)
    refine ⟨latO_mono (fun w hw => Sum.inl_injective hw.2) ha, ?_, latO_mono (fun w hw => hw.2) hb, ?_⟩
    · rw [wAt_eq_smul, smul_smul, hii]
    · rw [wAt_eq_smul, smul_sub, smul_smul, hii, sub_self]
  refine ⟨fun u hu => ?_, fun e he u hu hhu => ?_⟩
  · obtain ⟨ha, hia, hb, hib⟩ := split u hu
    have horth : symplO S T (2 • wAt (.inl v) u) (2 • (u - wAt (.inl v) u)) = 0 :=
      symplO_cut hci (by rw [smul_comm (idem D (.inl v)) (2 : ℕ), hia])
        (by rw [smul_comm (idem D (.inl v)) (2 : ℕ), hib, smul_zero])
    have hsum : 2 • u = 2 • wAt (.inl v) u + 2 • (u - wAt (.inl v) u) := by abel
    rw [hsum, GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T horth, hoff.1 _ hb, h2 _ ha hia]
  · obtain ⟨ha, hia, hb, hib⟩ := split u hu
    have heu : e • u = u := (GlobalTheory.SplitScalar.isHalf_iff e u).mp hhu
    have hea : e • wAt (.inl v) u = wAt (.inl v) u := by
      rw [wAt_eq_smul, smul_smul, mul_comm, ← smul_smul, heu]
    have heb : IsHalf e (u - wAt (.inl v) u) := by
      rw [GlobalTheory.SplitScalar.isHalf_iff, smul_sub, heu, hea]
    have horth : symplO S T (wAt (.inl v) u) (u - wAt (.inl v) u) = 0 := symplO_cut hci hia hib
    have hsum : u = wAt (.inl v) u + (u - wAt (.inl v) u) := by abel
    rw [hsum, GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T horth, hoff.2 e he _ hb heb,
      hs e he _ ha hia ((GlobalTheory.SplitScalar.isHalf_iff e _).mpr hea)]

set_option maxHeartbeats 1000000 in

theorem mem_span_local : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ (v : FinPl D) (x : WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) x → x ∈ Submodule.span ℂ (Set.range fun w : WO S T => heisO ψ S T (wAt (.inl v) w) f₀) := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ hb v x hx
  obtain ⟨hii, hci, -⟩ := idem_fin D v
  have hψ := base_std hb
  have hθ := base_inf hb
  have hsdS : IsSelfDualC S ΛS := hb.2.2.1
  have hsdT : IsSelfDualC T ΛT := hb.2.2.2.1
  have hloc0 : IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) f₀ := base_isLocal hb (.inl v)
  have hvac0 : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f₀ := base_vacAt hb (.inl v)
  have hglob := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hsdS hsdT
  have hcl : ∀ f, IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) f →
      (∀ w : WO S T, IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) (heisO ψ S T (wAt (.inl v) w) f)) ∧
      (∀ (c : ℂ) g, IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) g →
        IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) (c • f + g)) := fun f hf =>
    ⟨((GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hψ hθ f hf.1).2 (.inl v) hf).1,
      ((GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hψ hθ f hf.1).2 (.inl v) hf).2.1⟩
  have h0loc : IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) 0 := by
    have h := (hcl f₀ hloc0).2 (-1) f₀ hloc0
    simpa using h
  have hvAll0 : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀ :=
    isLatVac_latO_of_local_conditions v f₀ hloc0.2.1 (fun a ha _ => hvac0.1 a ha) (fun e he a ha _ hh => hvac0.2 e he a ha hh) _
  let Msub : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {f | IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) f}
      add_mem' := fun {f g} hf hg => by
        have h := (hcl f hf).2 1 g hg
        simpa using h
      zero_mem' := h0loc
      smul_mem' := fun c f hf => by
        have h := (hcl f hf).2 c 0 h0loc
        simpa using h }
  let X := cutPts S T (idem D (.inl v))
  let ρ : ↥X → ↥Msub →ₗ[ℂ] ↥Msub := fun y =>
    { toFun := fun m => ⟨heisO ψ S T (y : WO S T) m, by
        have hy : idem D (.inl v) • (y : WO S T) = y := y.2
        have h := (hcl m m.2).1 y
        rwa [wAt_eq_smul, hy] at h⟩
      map_add' := fun m m' => Subtype.ext (by
        show heisO ψ S T (y : WO S T) ((m : WO S T → ℂ) + m') = heisO ψ S T y m + heisO ψ S T y m'
        rw [← GlobalTheory.SplitScalar.heisL_apply, map_add, GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply])
      map_smul' := fun c m => Subtype.ext (by
        show heisO ψ S T (y : WO S T) (c • (m : WO S T → ℂ)) = c • heisO ψ S T y m
        exact GlobalTheory.SplitScalar.heisO_smul ψ S T y c m) }
  let e0 : ↥Msub := ⟨f₀, hloc0⟩
  let β : ↥X → ↥X → ℂ := fun y z => ψ (symplOH S T y z)
  let Λ : AddSubgroup ↥X := (latO S T ΛS ΛT fun u => u = v).comap X.subtype
  have hl : ∀ a b c : ↥X, β (a + b) c = β a c * β b c := fun a b c => by
    show ψ (symplOH S T ((a + b : ↥X) : WO S T) c) = ψ (symplOH S T a c) * ψ (symplOH S T b c)
    rw [AddSubgroup.coe_add, GlobalTheory.SplitScalar.symplOH_add_left, AddChar.map_add_eq_mul]
  have hr : ∀ a b c : ↥X, β a (b + c) = β a b * β a c := fun a b c => by
    show ψ (symplOH S T a ((b + c : ↥X) : WO S T)) = ψ (symplOH S T a b) * ψ (symplOH S T a c)
    rw [AddSubgroup.coe_add, GlobalTheory.SplitScalar.symplOH_add_right, AddChar.map_add_eq_mul]
  have hd : ∀ a : ↥X, β a a = 1 := fun a => by
    show ψ (symplOH S T a a) = 1
    rw [eq_zero_of_eq_neg_AF _ (GlobalTheory.SplitScalar.symplOH_skew S T a a), AddChar.map_zero_eq_one]
  have h0 : ∀ m : ↥Msub, ρ 0 m = m := fun m => Subtype.ext (by
    show heisO ψ S T ((0 : ↥X) : WO S T) m = m
    rw [AddSubgroup.coe_zero, GlobalTheory.SplitScalar.heisO_zero])
  have hρ : ∀ (a b : ↥X) (m : ↥Msub), ρ a (ρ b m) = β a b • ρ (a + b) m := fun a b m => Subtype.ext (by
    show heisO ψ S T a (heisO ψ S T b m) = ψ (symplOH S T a b) • heisO ψ S T ((a + b : ↥X) : WO S T) m
    rw [AddSubgroup.coe_add]
    exact GlobalTheory.SplitScalar.heisO_heisO ψ S T a b m)
  have hsq : ∀ y z : ↥X, β y z ^ 2 = ψ (symplO S T y z) := fun y z => by
    show ψ (symplOH S T y z) ^ 2 = _
    rw [sq, ← AddChar.map_add_eq_mul, GlobalTheory.SplitScalar.symplOH_add_self]
  have hΛ : ∀ y : ↥X, y ∈ Λ ↔ ∀ a ∈ Λ, β y a ^ 2 = 1 := by
    intro y
    constructor
    · intro hy a ha
      have hy' : (y : WO S T) ∈ latO S T ΛS ΛT (fun u => u = v) := hy
      have ha' : (a : WO S T) ∈ latO S T ΛS ΛT (fun u => u = v) := ha
      rw [hsq]
      have hyall := GlobalTheory.PlaceModel.latO_le_top _ hy'
      exact ((hglob.1 _ (GlobalTheory.SplitScalar.latO_fin hyall)).mp hyall) _ (GlobalTheory.PlaceModel.latO_le_top _ ha')
    · intro h
      have hε0 : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
        ⟨singleV D.host.F v 1, rfl, GlobalTheory.LatticeLocal.ev_self D.host.F v,
          fun w hw => GlobalTheory.LatticeLocal.ev_ne D.host.F hw⟩
      have hm := GlobalTheory.PlaceModel.mem_of_dual (ψ := ψ) hε0 hglob.1 (a := idem D (.inl v)) hii hii
        (by rw [hci]; exact hii) (y : WO S T) ((GlobalTheory.PlaceModel.mem_half S T).mpr y.2)
        (fun z hz => by
          have hz2 : idem D (.inl v) • z = z := by
            have h3 := (GlobalTheory.PlaceModel.mem_half S T).mp (AddSubgroup.mem_inf.mp hz).2
            rwa [hci] at h3
          have h4 := h ⟨z, hz2⟩ (AddSubgroup.mem_inf.mp hz).1
          rwa [hsq] at h4)
      exact (AddSubgroup.mem_inf.mp hm).1
  have hdiv : ∀ N : ℕ, 0 < N → ∀ y : ↥X, ∃ z : ↥X, N • z = y := fun N hN y => by
    obtain ⟨z, hz, hzN⟩ := GlobalTheory.PlaceModel.half_div S T (idem D (.inl v)) N hN (y : WO S T)
      ((GlobalTheory.PlaceModel.mem_half S T).mpr y.2)
    exact ⟨⟨z, (GlobalTheory.PlaceModel.mem_half S T).mp hz⟩, Subtype.ext (by rw [AddSubgroup.coe_nsmul]; exact hzN)⟩
  have hFGS : ΛS.FG := hsdS.1.fg
  have hFGT : ΛT.FG := hsdT.1.fg
  have hfin : ∀ N : ℕ, 0 < N → ∃ R : Set ↥X, R.Finite ∧ ∀ t ∈ Λ, ∃ r ∈ R, ∃ u ∈ Λ, t = r + N • u := by
    intro N hN
    obtain ⟨R0, hR0, hR0m⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T ΛS ΛT hFGS hFGT (fun u => u = v) N hN
    have hcut : ∀ w : WO S T, idem D (.inl v) • (idem D (.inl v) • w) = idem D (.inl v) • w := fun w => by
      rw [smul_smul, hii]
    refine ⟨(fun r => (⟨idem D (.inl v) • r, hcut r⟩ : ↥X)) '' R0, hR0.image _, ?_⟩
    intro t ht
    obtain ⟨r, hr, u, hu, htu⟩ := hR0m (t : WO S T) ht
    have hu' : idem D (.inl v) • u ∈ latO S T ΛS ΛT (fun w => w = v) := by
      rw [← wAt_eq_smul]
      exact latO_mono (fun w hw => Sum.inl_injective hw.2)
        (GlobalTheory.LatticeLocal.wAt_mem_latO D S T ΛS ΛT (fun w => w = v) u hu (.inl v)).1
    refine ⟨⟨idem D (.inl v) • r, hcut r⟩, ⟨r, hr, rfl⟩, ⟨idem D (.inl v) • u, hcut u⟩, hu', ?_⟩
    apply Subtype.ext
    rw [AddSubgroup.coe_add, AddSubgroup.coe_nsmul]
    show (t : WO S T) = idem D (.inl v) • r + N • (idem D (.inl v) • u)
    have ht2 : idem D (.inl v) • (t : WO S T) = t := t.2
    rw [← ht2, htu, smul_add, smul_comm (idem D (.inl v)) N u]
  have he : e0 ≠ 0 := fun h => base_ne_zero hb (congrArg Subtype.val h)
  have hε : ∀ u ∈ Λ, ∃ ε : ℂ, ρ u e0 = ε • e0 := fun u hu => by
    have hu' : (u : WO S T) ∈ latO S T ΛS ΛT (fun w => w = v) := hu
    obtain ⟨ε, -, hε⟩ := hglob.2.2 f₀ hvAll0 u (GlobalTheory.PlaceModel.latO_le_top _ hu')
    exact ⟨ε, Subtype.ext (hε f₀ hvAll0)⟩
  have h2 : ∀ u ∈ Λ, ρ (2 • u) e0 = e0 := fun u hu => Subtype.ext (by
    show heisO ψ S T ((2 • u : ↥X) : WO S T) f₀ = f₀
    rw [AddSubgroup.coe_nsmul]
    exact hvac0.1 _ hu)
  have hvac : ∀ m : ↥Msub, (∀ u ∈ Λ, ∀ ε : ℂ, ρ u e0 = ε • e0 → ρ u m = ε • m) → ∃ c : ℂ, m = c • e0 := by
    intro m hm
    have hmloc : IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) m := m.2
    have hmAll : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) m := by
      refine isLatVac_latO_of_local_conditions (ψ := ψ) (S := S) (T := T) (ΛS := ΛS) (ΛT := ΛT) v (m : WO S T → ℂ) hmloc.2.1 (fun a ha hia => ?_) (fun e he a ha hia hh => ?_) _
      · have h2a : idem D (.inl v) • (2 • a) = 2 • a := by
          rw [smul_comm (idem D (.inl v)) (2 : ℕ), hia]
        have h3 := hm ⟨2 • a, h2a⟩ (nsmul_mem ha 2) 1 (Subtype.ext (by
          show heisO ψ S T (2 • a) f₀ = (1 : ℂ) • f₀
          rw [one_smul]
          exact hvac0.1 a ha))
        have h4 : heisO ψ S T (2 • a) m = (1 : ℂ) • (m : WO S T → ℂ) := congrArg Subtype.val h3
        rwa [one_smul] at h4
      · have h3 := hm ⟨a, hia⟩ ha 1 (Subtype.ext (by
          show heisO ψ S T a f₀ = (1 : ℂ) • f₀
          rw [one_smul]
          exact hvac0.2 e he a ha hh))
        have h4 : heisO ψ S T a m = (1 : ℂ) • (m : WO S T → ℂ) := congrArg Subtype.val h3
        rwa [one_smul] at h4
    obtain ⟨c, hc⟩ := GlobalTheory.VacuumLine.eq_smul_base D ψ θ S T sS sT ΛS ΛT f₀ hb m hmloc.1 hmAll
      (fun τ => hmloc.2.2 τ Sum.inr_ne_inl)
    exact ⟨c, Subtype.ext hc⟩
  have hv : ∃ N : ℕ, 0 < N ∧ ∀ u ∈ Λ, ρ (N • u) ⟨x, hx⟩ = ⟨x, hx⟩ := by
    obtain ⟨U, hUo, hU⟩ := hx.1.level
    obtain ⟨N, hN, hNU⟩ :=
      (GlobalTheory.T.completedHomLattice_multiple_mem_open_level D S T ΛS ΛT hsdS hsdT (GlobalTheory.T.completedHomLattice_finitelyGenerated D S T ΛS ΛT hsdS hsdT)).1 U hUo
    refine ⟨N, hN, fun u hu => Subtype.ext ?_⟩
    have hu' : (u : WO S T) ∈ latO S T ΛS ΛT (fun w => w = v) := hu
    have hall := GlobalTheory.PlaceModel.latO_le_top _ hu'
    show heisO ψ S T ((N • u : ↥X) : WO S T) x = x
    rw [AddSubgroup.coe_nsmul]
    exact hU _ (hNU _ hall) (GlobalTheory.SplitScalar.latO_fin (nsmul_mem hall N))
  have hmem := GlobalTheory.HeisVacuum.mem_span_translates_vacuum ↥X ↥Msub β ρ Λ e0 hl hr hd h0 hρ hΛ hdiv hfin he
    hε h2 hvac ⟨x, hx⟩ hv
  have hmap := Submodule.mem_map_of_mem (f := Msub.subtype) hmem
  rw [← Submodule.span_image] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
  refine ⟨(y : WO S T), ?_⟩
  have hy : idem D (.inl v) • (y : WO S T) = y := y.2
  show heisO ψ S T (wAt (.inl v) (y : WO S T)) f₀ = heisO ψ S T (y : WO S T) f₀
  rw [wAt_eq_smul, hy]

end GlobalTheory.LocalSpan

end
