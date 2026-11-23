import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Stages2L

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.WeilFull

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat

variable {R : RealDat D A Ks} {F : Face D A}

theorem preliminary_of_vacuum_update (h : R.Pre1 F) (ωY ωX vac vacX vY vX ItY ItX ioY ioX Th) : (R.upd3 ωY ωX vac vacX vY vX ItY ItX ioY ioX Th).Pre1 F :=
  ⟨⟨h.1.lev, h.1.red_R, h.1.red_L, h.1.levels, h.1.record, ⟨h.1.fam.tie, h.1.fam.Sb, h.1.fam.roots, h.1.fam.pl_onto, h.1.fam.degR, h.1.fam.degL, h.1.fam.muVal, h.1.fam.etaVal⟩, h.1.inf, h.1.vpos, h.1.cX, h.1.cV, h.1.prX, h.1.order, h.1.std⟩,
    ⟨h.2.inf, h.2.vpos, h.2.cX, h.2.cV, h.2.prX, h.2.HX, h.2.HV, h.2.HE, h.2.HW, h.2.gE, h.2.gW, h.2.jX, h.2.jV, h.2.νY, h.2.νY', h.2.ν0, h.2.νX, h.2.νV, h.2.νW, h.2.BV, h.2.order⟩⟩

theorem preliminary_of_frame_update (h : R.Pre1 F) (ωP vacP vP ioP thF thG) : (R.upd4 ωP vacP vP ioP thF thG).Pre1 F :=
  ⟨⟨h.1.lev, h.1.red_R, h.1.red_L, h.1.levels, h.1.record, ⟨h.1.fam.tie, h.1.fam.Sb, h.1.fam.roots, h.1.fam.pl_onto, h.1.fam.degR, h.1.fam.degL, h.1.fam.muVal, h.1.fam.etaVal⟩, h.1.inf, h.1.vpos, h.1.cX, h.1.cV, h.1.prX, h.1.order, h.1.std⟩,
    ⟨h.2.inf, h.2.vpos, h.2.cX, h.2.cV, h.2.prX, h.2.HX, h.2.HV, h.2.HE, h.2.HW, h.2.gE, h.2.gW, h.2.jX, h.2.jV, h.2.νY, h.2.νY', h.2.ν0, h.2.νX, h.2.νV, h.2.νW, h.2.BV, h.2.order⟩⟩

theorem full_Y_of_theta_update (h : R.FullY) (ωP vacP vP ioP thF thG) : (R.upd4 ωP vacP vP ioP thF thG).FullY := h

theorem preliminary_of_index_update (h : R.Pre1 F) (nW FW mu twPl err0) : (R.upd5 nW FW mu twPl err0).Pre1 F :=
  ⟨⟨h.1.lev, h.1.red_R, h.1.red_L, h.1.levels, h.1.record, ⟨h.1.fam.tie, h.1.fam.Sb, h.1.fam.roots, h.1.fam.pl_onto, h.1.fam.degR, h.1.fam.degL, h.1.fam.muVal, h.1.fam.etaVal⟩, h.1.inf, h.1.vpos, h.1.cX, h.1.cV, h.1.prX, h.1.order, h.1.std⟩,
    ⟨h.2.inf, h.2.vpos, h.2.cX, h.2.cV, h.2.prX, h.2.HX, h.2.HV, h.2.HE, h.2.HW, h.2.gE, h.2.gW, h.2.jX, h.2.jV, h.2.νY, h.2.νY', h.2.ν0, h.2.νX, h.2.νV, h.2.νW, h.2.BV, h.2.order⟩⟩

theorem full_Y_of_index_update (h : R.FullY) (nW FW mu twPl err0) : (R.upd5 nW FW mu twPl err0).FullY := h

theorem full_P_of_index_update (h : R.FullP) (nW FW mu twPl err0) : (R.upd5 nW FW mu twPl err0).FullP := h

theorem preliminary_of_scalar_update (h : R.Pre1 F) (kap lam) : (R.upd6 kap lam).Pre1 F :=
  ⟨⟨h.1.lev, h.1.red_R, h.1.red_L, h.1.levels, h.1.record, ⟨h.1.fam.tie, h.1.fam.Sb, h.1.fam.roots, h.1.fam.pl_onto, h.1.fam.degR, h.1.fam.degL, h.1.fam.muVal, h.1.fam.etaVal⟩, h.1.inf, h.1.vpos, h.1.cX, h.1.cV, h.1.prX, h.1.order, h.1.std⟩,
    ⟨h.2.inf, h.2.vpos, h.2.cX, h.2.cV, h.2.prX, h.2.HX, h.2.HV, h.2.HE, h.2.HW, h.2.gE, h.2.gW, h.2.jX, h.2.jV, h.2.νY, h.2.νY', h.2.ν0, h.2.νX, h.2.νV, h.2.νW, h.2.BV, h.2.order⟩⟩

theorem chain_of_scalar_update (h : R.IsChain) (kap lam) : (R.upd6 kap lam).IsChain :=
  ⟨h.ωY, h.ωX, h.vY, h.vX, h.ptY, h.ptX, h.ItY, h.ItX, h.ioY, h.ioX, h.Th⟩

theorem full_Y_of_scalar_update (h : R.FullY) (kap lam) : (R.upd6 kap lam).FullY := h

theorem theta_props_of_scalar_update (h : R.IsThP) (kap lam) : (R.upd6 kap lam).IsThP :=
  ⟨h.ωP, h.vP, h.pt_theta, h.ioP, h.thF_mem, h.thF, h.thG⟩

theorem full_P_of_scalar_update (h : R.FullP) (kap lam) : (R.upd6 kap lam).FullP := h

theorem complex_side_of_scalar_update (kap lam) : (R.upd6 kap lam).toCx F = reScal (R.toCx F) (fun _ => kap) lam := rfl

end RealDat

end Stages2L

section Stages3

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.WeilFull Formalism.IndefR.Fin

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {F : Face D A}

theorem exists_cond {X : Sort*} (x₀ : X) {c : Prop} {p : X → Prop} (h : c → ∃ x, p x) : ∃ x, c → p x := by
  by_cases hc : c
  · obtain ⟨x, hx⟩ := h hc; exact ⟨x, fun _ => hx⟩
  · exact ⟨x₀, fun h' => absurd h' hc⟩

theorem HMod.factor {X Z : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Z] [Module ℂ Z] (M : HMod Z) {V : Submodule ℂ Z}
    {ip : Z → Z → ℂ} (hM : M.Is V ip) (f : X →ₗ[ℂ] Z) (hf : ∀ x, f x ∈ V) : ∃ g : X →ₗ[ℂ] M.H, ∀ x, M.e (g x) = f x :=
  exists_factor M.e hM.1 f fun x => hM.2.1 ▸ hf x

theorem thDn_mem (R : RealDat D A Ks) (t : T) (x : (R.HX t).H) : R.thDn t x ∈ R.CC t 0 :=
  (Lift.thetaDn (R.CC t) (R.ioY t) (D.R.m - 1) (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict x))).2

theorem th_exists (hG : GoodLands D A Ks F) (R : RealDat D A Ks) (h : R.Pre1 F) (t : T) :
    ∃ g : (R.HX t).H →ₗ[ℂ] R.HE.H, ∀ x, R.HE.e (g x) = postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm (R.thDn t x)) :=
  R.HE.factor h.2.HE (postOn (R.MY 0) R.e0 ∘ₗ
    (PiTensorProduct.lift.symm : (SmT (R.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) ≃ₗ[ℂ] MMap (R.MY 0)).toLinearMap ∘ₗ R.thDn t)
    fun x => (hG R h).1 t _ (thDn_mem R t x)

theorem kerY_args (hW : WeilExistsFull D) (hV : VacExistsO D) (hS : StepVecExists D) (hPt : PtStable D) (hC : CartanOK D)
    (hD : SelfDualOK D) (hT : Formalism.IndefR.Fin.VecThetaSD D) (hF : SeedFacts D A Ks F) (R : RealDat D A Ks) (h : R.Pre1 F) :
    ∃ ωY ωX vac vacX vY vX, (R.upd3 ωY ωX vac vacX vY vX R.ItY R.ItX R.ioY R.ioX R.Th).KerY := by
  obtain ⟨hsp, hid⟩ := hF R h.1
  have hm : D.R.m - 1 < D.R.m := Nat.sub_lt (lt_of_lt_of_le two_pos D.R.two_le_m) one_pos
  have sd : ∀ j, j < D.R.m → IsSelfDualC (Yc D j) (R.ΛY j) ∧ IsFrame (R.βY j) (R.ΛY j) := fun j hj => by
    obtain ⟨c, hc⟩ := h.1.lev.βY j hj
    exact ⟨hD _ _ _ _ hc, hc.1⟩
  have sdX : IsSelfDualC D.sp.X' R.ΛX ∧ IsFrame R.βX R.ΛX := by
    obtain ⟨c, hc⟩ := h.1.lev.βX
    exact ⟨hD _ _ _ _ hc, hc.1⟩
  choose ωY hωY using fun t k => exists_cond (1 : GA D (Yc D k) × GA D (Yc D (k + 1)) →* Module.End ℂ (WO (Yc D k) (Yc D (k + 1)) → ℂ))
    fun hk : k + 1 < D.R.m => hW R.ψ _ _ _ _ h.1.std ((hsp t).1 k hk).1 ((hsp t).1 k hk).2.1 ((hsp t).1 k hk).2.2.1 ((hsp t).1 k hk).2.2.2
  choose ωX hωX using fun t => hW R.ψ (Yc D (D.R.m - 1)) D.sp.X' _ _ h.1.std (hsp t).2.1.1 (hsp t).2.1.2.1 (hsp t).2.1.2.2.1
    (hsp t).2.1.2.2.2
  choose vac hvac using fun k => exists_cond (0 : WO (Yc D k) (Yc D (k + 1)) → ℂ) fun hk : k + 1 < D.R.m =>
    hV R.ψ R.θ h.1.std h.1.inf (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (D.sp.Y_sig _) (D.sp.Y_sig _)
      (hC.1 _ _ _ (D.sp.Y_sig _)) (hC.1 _ _ _ (D.sp.Y_sig _)) (R.ΛY k) (R.ΛY (k + 1)) (sd k (by omega)).1 (sd (k + 1) hk).1
  obtain ⟨vacX, hvacX⟩ := hV R.ψ R.θ h.1.std h.1.inf (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX)
    (D.sp.Y_sig _) D.sp.X'_sig (hC.1 _ _ _ (D.sp.Y_sig _)) (hC.1 _ _ _ D.sp.X'_sig) (R.ΛY (D.R.m - 1)) R.ΛX (sd _ hm).1 sdX.1
  choose vY hvY using fun t k => exists_cond (0 : WO (Yc D k) (Yc D (k + 1)) → ℂ) fun hk : k + 1 < D.R.m =>
    hS R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (R.ΛY k) (R.ΛY (k + 1)) (R.βY k) (R.βY (k + 1))
      (R.datYt t k R.triv) (R.chi (k + 1)) (R.Q t) (R.xiR t) (sd k (by omega)).1 (sd (k + 1) hk).1 (sd k (by omega)).2 (sd (k + 1) hk).2
      (hid t).1 (hid t).2 (vac k) (hvac k hk)
  choose vX hvX using fun t =>
    hS R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX) (R.ΛY (D.R.m - 1)) R.ΛX (R.βY (D.R.m - 1)) R.βX
      (R.datYt t (D.R.m - 1) R.triv) (R.chi D.R.m) (R.Q t) (R.xiR t) (sd _ hm).1 sdX.1 (sd _ hm).2 sdX.2 (hid t).1
      (hid t).2 vacX hvacX
  exact ⟨ωY, ωX, vac, vacX, vY, vX, ⟨hωY, hωX⟩, hvY, hvX,
    fun t k hk P => hPt R.ψ R.θ h.1.std h.1.inf _ _ _ _ _ _ _ P (hT.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sd k (by omega)).1 (sd (k + 1) hk).1
      (sd k (by omega)).2 (sd (k + 1) hk).2 (hvY t k hk)),
    fun t P => hPt R.ψ R.θ h.1.std h.1.inf _ _ _ _ _ _ _ P (hT.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sd _ hm).1 sdX.1 (sd _ hm).2 sdX.2
      (hvX t))⟩

set_option maxHeartbeats 1000000 in

theorem chain_exists (hI : ItExists D A Ks F) (hO : IoChainExists D A Ks F) (hG : GoodLands D A Ks F) (R : RealDat D A Ks)
    (h : R.Pre1 F) (hK : R.KerY) : ∃ R' : RealDat D A Ks, R'.Pre1 F ∧ R'.IsChain ∧ R'.FullY := by
  obtain ⟨h1, ItX, hX⟩ := hI R h hK
  choose ItY hY using fun k => exists_cond (R.ItY k) (h1 k)
  let R1 := R.upd3 R.ωY R.ωX R.vac R.vacX R.vY R.vX ItY ItX R.ioY R.ioX R.Th
  have p1 : R1.Pre1 F := RealDat.preliminary_of_vacuum_update h _ _ _ _ _ _ _ _ _ _ _
  have k1 : R1.KerY := hK
  have o1 := hO R1 p1 k1 (fun t k hk => hY k hk t) hX
  choose ioY hioY using fun t k => exists_cond (R1.ioY t k) ((o1 t).1 k)
  choose ioX hioX using fun t => (o1 t).2
  let R2 := R.upd3 R.ωY R.ωX R.vac R.vacX R.vY R.vX ItY ItX ioY ioX R.Th
  have p2 : R2.Pre1 F := RealDat.preliminary_of_vacuum_update h _ _ _ _ _ _ _ _ _ _ _
  choose Th hTh using th_exists hG R2 p2
  refine ⟨R.upd3 R.ωY R.ωX R.vac R.vacX R.vY R.vX ItY ItX ioY ioX Th, RealDat.preliminary_of_vacuum_update h _ _ _ _ _ _ _ _ _ _ _,
    ⟨fun t k hk => (hK.1.1 t k hk).datum, fun t => (hK.1.2 t).datum, hK.2.1, hK.2.2.1, hK.2.2.2.1, hK.2.2.2.2,
      fun t k hk => hY k hk t, hX, fun t k hk => hioY t k (by omega), hioX, hTh⟩, hK.1⟩

theorem exists_localWeil_vacuum_kernel (hW : WeilExistsFull D) (hV : VacExistsO D) (hS : ThPVecExists D) (hPt : PtStable D) (hC : CartanOK D)
    (hD : SelfDualOK D) (hT : Formalism.IndefR.Fin.VecThetaSD D) (hF : SeedFacts D A Ks F) (R : RealDat D A Ks) (h : R.Pre1 F) :
    ∃ ωP vacP vP, (R.upd4 ωP vacP vP R.ioP R.thF R.thG).KerP := by
  obtain ⟨hsp, hid⟩ := hF R h.1
  have sdV : ∀ i, IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsFrame (R.βV i) (R.ΛV i) := fun i => by
    obtain ⟨c, hc⟩ := h.1.lev.βV i
    exact ⟨hD _ _ _ _ hc, hc.1⟩
  have sdW : ∀ i, IsSelfDualC (Wc D i) (R.ΛW i) ∧ IsFrame (R.βW i) (R.ΛW i) := fun i => by
    obtain ⟨c, hc⟩ := h.1.lev.βW i
    exact ⟨hD _ _ _ _ hc, hc.1⟩
  choose ωP hωP using fun (i : Fin D.R.m) t => hW R.ψ (Vc D i) (Wc D i) _ _ h.1.std ((hsp t).2.2 i).1 ((hsp t).2.2 i).2.1
    ((hsp t).2.2 i).2.2.1 ((hsp t).2.2 i).2.2.2
  choose vacP hvac using fun i : Fin D.R.m => hV R.ψ R.θ h.1.std h.1.inf (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A)))
    (D.sp.V_sig _) (D.sp.W_sig _) (hC.2 _ (D.sp.V_sig _) (h.1.vpos i)) (hC.1 _ _ _ (D.sp.W_sig _)) (R.ΛV i) (R.ΛW i) (sdV i).1 (sdW i).1
  choose vP hvP using fun (i : Fin D.R.m) t => hS R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i)
    (R.βV i) (R.βW i) R.Pg (R.Q t) (R.xiR t) (sdV i).1 (sdW i).1 (sdV i).2 (sdW i).2 (hid t).1 (hid t).2 (vacP i) (hvac i)
  exact ⟨ωP, vacP, vP, hωP, hvP, fun i t P => hPt R.ψ R.θ h.1.std h.1.inf _ _ _ _ _ _ _ P
    (hT.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sdV i).1 (sdW i).1 (sdV i).2 (sdW i).2 (hvP i t))⟩

end Stages3

section Stages4

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.WeilFull Formalism.IndefR.Fin

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {F : Face D A}

theorem exists_val {p : ℝ → Prop} (hu : ∀ l l', p l → p l' → l = l') (d : ℝ) : ∃ x, (∀ l, p l → x = l) ∧ ((∀ l, ¬ p l) → x = d) := by
  by_cases h : ∃ l, p l
  · obtain ⟨l, hl⟩ := h
    exact ⟨l, fun l' hl' => hu _ _ hl hl', fun hn => absurd hl (hn l)⟩
  · exact ⟨d, fun l hl => absurd ⟨l, hl⟩ h, fun _ => rfl⟩

namespace RealDat

variable (R : RealDat D A Ks) (F)

def Eig0 (i : Fin D.R.m) (t : T) (p : A.fam.base.Ix) (l : ℝ) : Prop :=
  R.Wp i p ≠ ⊥ ∧ ∀ x ∈ R.Wp i p, R.thG i t (LinearMap.adjoint (R.thG i t) x) = (l : ℂ) • x

def EigOff (i : Fin D.R.m) (p : A.fam.base.Ix) (v : InfinitePlace D.what₂.LL) (l : ℝ) : Prop :=
  ∃ b, PartX F.cr (R.toCx F) b i p v ∧ (b = false ∨ ¬ PartX F.cr (R.toCx F) false i p v) ∧ SimX F.cr (R.toCx F) b i p v l

variable {R F}

theorem base_eigenvalue_unique {i t p} (l l' : ℝ) (h : R.Eig0 i t p l) (h' : R.Eig0 i t p l') : l = l' := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.1
  have := (h.2 x hx).symm.trans (h'.2 x hx)
  exact_mod_cast smul_left_injective ℂ hx0 this

theorem eigOff_unique {i p v} (l l' : ℝ) (h : R.EigOff F i p v l) (h' : R.EigOff F i p v l') : l = l' := by
  obtain ⟨b, hp, hb, he⟩ := h
  obtain ⟨b', hp', hb', he'⟩ := h'
  have hbb : b = b' := by
    cases b <;> cases b'
    · rfl
    · rcases hb' with h | h
      · exact absurd h (by decide)
      · exact absurd hp h
    · rcases hb with h | h
      · exact absurd h (by decide)
      · exact absurd hp' h
    · rfl
  subst hbb
  obtain ⟨x, hx, hx0⟩ := hp
  have := (he x hx x).symm.trans (he' x hx x)
  exact_mod_cast mul_right_cancel₀ hx0 this

theorem part_at_of_scalar_update (kap lam b i p v) : (R.upd6 kap lam).PartAt F b i p v ↔ PartX F.cr (R.toCx F) b i p v := by
  change PartX F.cr ((R.upd6 kap lam).toCx F) b i p v ↔ _
  rw [complex_side_of_scalar_update, partX_reScal]

theorem similarity_of_scalar_update (kap lam b i p v l) : SimX F.cr ((R.upd6 kap lam).toCx F) b i p v l ↔ SimX F.cr (R.toCx F) b i p v l := by
  rw [complex_side_of_scalar_update, simX_reScal]

theorem subspaces_of_scalar_update (kap lam) : ((R.upd6 kap lam).toCx F).zs = (R.toCx F).zs := by
  rw [complex_side_of_scalar_update, zs_reScal]

end RealDat

open Classical in

theorem scal_exists (R : RealDat D A Ks) : ∃ kap lam, (R.upd6 kap lam).IsScal F := by
  choose l0 h0 h0' using fun i t p => exists_val (p := R.Eig0 i t p) RealDat.base_eigenvalue_unique (Real.exp ((F.Zsc (R.toCx F).zs).l6m i))
  choose l1 h1 h1' using fun i p v => exists_val (p := R.EigOff F i p v) RealDat.eigOff_unique (Real.exp ((F.Zsc (R.toCx F).zs).l6m i))
  let lam : Fin D.R.m → T → A.fam.base.Ix → InfinitePlace D.what₂.LL → ℝ := fun i t p v => if v = A.v0 then l0 i t p else l1 i p v
  let R1 := R.upd6 R.kap lam
  obtain ⟨kap, hk, -⟩ := exists_val (p := fun κ => Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp R1.lamN κ ∧
      ∃ t p, R.EEp p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, R1.lamN t j p ≠ 0) (fun κ κ' h h' => by
    obtain ⟨t, p, hp, hne⟩ := h.2
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
    have := (h.1 t p x hx).symm.trans (h'.1 t p x hx)
    have h2 : κ * ∏ j ∈ Finset.Icc 1 D.R.m, R1.lamN t j p = κ' * ∏ j ∈ Finset.Icc 1 D.R.m, R1.lamN t j p := by
      exact_mod_cast smul_left_injective ℂ hx0 this
    exact mul_right_cancel₀ hne h2) 1
  refine ⟨kap, lam, fun i t p l hp hl => ?_, fun κ h h' => hk κ ⟨h, h'⟩, fun b i p v l hv hp hb he => ?_, fun i t p hp => ?_,
    fun i p v hv hp => ?_, fun i t p v hv => ?_⟩
  · exact (if_pos rfl).trans (h0 i t p l ⟨hp, hl⟩)
  · exact (if_neg hv).trans (h1 i p v l ⟨b, (RealDat.part_at_of_scalar_update _ _ _ _ _ _).1 hp,
      hb.imp id fun hn hh => hn ((RealDat.part_at_of_scalar_update _ _ _ _ _ _).2 hh), (RealDat.similarity_of_scalar_update _ _ _ _ _ _ _).1 he⟩)
  · rw [RealDat.subspaces_of_scalar_update]
    exact (if_pos rfl).trans (h0' i t p fun l hl => hl.1 hp)
  · rw [RealDat.subspaces_of_scalar_update]
    exact (if_neg hv).trans (h1' i p v fun l hl => by
      obtain ⟨b, hb, -⟩ := hl
      exact hp b ((RealDat.part_at_of_scalar_update _ _ _ _ _ _).2 hb))
  · exact (if_neg hv).trans (if_neg hv).symm

variable (D A Ks) in

def SeedExists (F : Face D A) : Prop := ∃ R : RealDat D A Ks, R.Pre0 F

variable (D A Ks) in

def ModelsExist (F : Face D A) : Prop := ∀ R : RealDat D A Ks, R.Pre0 F → ∃ R' : RealDat D A Ks, R'.Pre1 F

variable (D A Ks) in

def ArithExists (F : Face D A) : Prop :=
  ∀ R : RealDat D A Ks, R.Pre1 F → R.IsChain → R.FullY → R.IsThP → R.FullP →
    ∃ nW FW mu twPl err0, (R.upd5 nW FW mu twPl err0).grp_chiW ∧ (R.upd5 nW FW mu twPl err0).IsTup F

end Stages4

end Formalism.IndefR.Links

end
