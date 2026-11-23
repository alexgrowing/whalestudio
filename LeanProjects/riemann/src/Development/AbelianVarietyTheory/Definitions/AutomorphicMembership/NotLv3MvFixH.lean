import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfMulJ0Decoration
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameFOfDiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralComparisonTransportedDivisionLatticeChan

noncomputable section

namespace GlobalTheory.Mem.SRe.CarModel

section Pts
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem pt_swap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) {n : ℕ}
    [NeZero n] {ST SG Q Q' : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q' = ∅) {y k k' g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q}
    {q : DecoF E n ST SG Q'} (h : IsPtOf hc (y * k) p) (h' : IsPtOf hc (y * k') p) (hq : IsPtOf hc (g * k) q) :
    IsPtOf hc (g * k') q := by
  have e : ∀ a : GL (Fin n) (AfE F E), a * k * (k⁻¹ * k') = a * k' := fun a => by group
  obtain ⟨hz, hr⟩ := ((isPtOf_mul_J0 F E hc n ST SG Q (y * k) (k⁻¹ * k') p p 1).1 h (by rw [e]; exact h')).2 (one_smul _ _).symm
  have := (isPtOf_mul_J0 F E hc n ST SG Q' (g * k) (k⁻¹ * k') q q 1).2.1 hQ hq hz hr
  rw [e] at this
  exact (one_smul _ q : ((1, 1, 1) : UF E n × GLG E n SG × GLQ E n Q') • q = q) ▸ this

set_option maxHeartbeats 2000000 in

theorem reads_le {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (i : ℕ) {Lb Lb'} {U U' : Subgroup (GA B (B.R.N i))}
    {chi : U →* ℂˣ} {chi' : U' →* ℂˣ} {y y' st st' k k'} (hy : y' = y)
    (h : I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st k)
    (h' : I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb') (fun _ => U') (fun _ => chi') y' st' k')
    (hU : U ≤ UAd B.sp.cm (B.R.N i)) (x : U) : ∃ hx : x.1 ∈ U', chi' ⟨x.1, hx⟩ = chi x := by
  subst hy
  rename' y' => y
  obtain ⟨c, -⟩ := h.onto ()
  have hQ : QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := by
    rw [I.trueColumn_tuple_trivial_eq_one]
    exact twistPrimes_trivialTuple_empty I.sel I.S
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  obtain ⟨p0, hp0, -⟩ := h.k_std ()
  have hk : k () ∈ UAd B.sp.cm (B.R.N i) := hp0.uni
  have hyk : y c * k () ∈ UAd B.sp.cm (B.R.N i) := (h.pt c).uni
  have hg : y c * x.1 * k () ∈ UAd B.sp.cm (B.R.N i) := by
    have h1 : y c * x.1 * k () = (y c * k ()) * ((k ())⁻¹ * x.1 * k ()) := by group
    rw [h1]
    exact mul_mem hyk (mul_mem (mul_mem (inv_mem hk) (hU x.2)) hk)
  obtain ⟨q₁, hq₁, -⟩ := exists_near (ST := (B.primes X).vT u) (SG := (B.primes X).vGs)
    (Q := QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K)) B.sp.cm 0 hg
  have hq : IsPtOf B.sp.cm (y c * x.1 * k ()) q₁ :=
    (GlobalTheory.Mem.Col2.PtDeco.isPtOf_iff_decoRaw _ _ B.sp.cm _ _ _ _ _ q₁ hQ).2 ⟨hg, hq₁.symm⟩
  have hq' : IsPtOf B.sp.cm (y c * x.1 * k' ()) q₁ := pt_swap B.sp.cm hQ (h.pt c) (h'.pt c) hq
  have hm := (h.lev c x.1 q₁ hq).1 x.2
  have hx : x.1 ∈ U' := (h'.lev c x.1 q₁ hq').2 hm
  obtain ⟨κ, hgam, hκq, -⟩ := hm
  refine ⟨hx, Units.ext ?_⟩
  exact (h'.chr c ⟨x.1, hx⟩ κ hgam (by rw [hκq]; exact hq')).trans (h.chr c x κ hgam (by rw [hκq]; exact hq)).symm

theorem heq_chi {G : Type} [Group G] {U U' : Subgroup G} {chi : U →* ℂˣ} {chi' : U' →* ℂˣ}
    (h : ∀ x : U, ∃ hx : x.1 ∈ U', chi' ⟨x.1, hx⟩ = chi x) (h' : ∀ x : U', ∃ hx : x.1 ∈ U, chi ⟨x.1, hx⟩ = chi' x) :
    U' = U ∧ HEq chi' chi := by
  have e : U' = U := le_antisymm (fun x hx => (h' ⟨x, hx⟩).1) (fun x hx => (h ⟨x, hx⟩).1)
  subst e
  exact ⟨rfl, heq_of_eq (MonoidHom.ext fun x => (h x).2)⟩

end Pts

section Std
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.ColAd Formalism.L2.Col
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

set_option maxHeartbeats 4000000 in

theorem U_le (Z : w.Lt) (u : B.Word) (F : Forms0 (w.D Z) u) :
    (show Subgroup (GA B (B.R.N 0)) from F.cls0.lev.U) ≤ UAd B.sp.cm (B.R.N 0) := by
  have hg1 : gramN (w.D Z) 0 (Nat.zero_le _) = 1 := ((spaces_in_coordinates w.I w.ok w.pins w.l Z).2.2.2 0 (Nat.zero_le _)).1
  have eU : UPts (sigD (w.D Z)) (gramN (w.D Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (w.D Z).host.F) (w.D Z).host.F) =
      UAd B.sp.cm (B.R.N 0) := by rw [hg1]; rfl
  exact fun x hx => eU ▸ ((F.cls0.lev.U_eq x).1 hx).1

abbrev Car (B : Base) : Type :=
  Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E) × Σ U : Subgroup (GA B (B.R.N 0)), (U →* ℂˣ)

set_option maxHeartbeats 4000000 in

def car (Z : w.Lt) (u : B.Word)
    (S : StepLevel (w.D Z).host.F (w.D Z).host.E (sigD (w.D Z)) (gramN (w.D Z) 0 (Nat.zero_le _)) ((w.D Z).mem u).A.T (w.D Z).R.f
      (badG (w.D Z))) : Car B := (S.Lb, ⟨S.U, S.chi⟩)

set_option maxHeartbeats 4000000 in

theorem car_eq {Z Z' : w.Lt} (t : ColT w Z) (t' : ColT w Z') (u : B.Word) :
    car Z' u (t'.C.forms u).to0.cls0.lev = car Z u (t.C.forms u).to0.cls0.lev := by
  obtain ⟨k, h⟩ := (t.std u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  obtain ⟨k', h'⟩ := (t'.std u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hy := (funext ((t.std u).yE 0 (Nat.zero_le _) (Or.inl rfl))).trans (funext ((t'.std u).yE 0 (Nat.zero_le _) (Or.inl rfl))).symm
  have e := heq_chi (reads_le w.I u 0 hy.symm h h' (U_le Z u (t.C.forms u).to0)) (reads_le w.I u 0 hy h' h (U_le Z' u (t'.C.forms u).to0))
  exact Prod.ext (Submodule.ext fun x => (h'.lb () x).trans (h.lb () x).symm) (Sigma.ext e.1 e.2)

set_option maxHeartbeats 4000000 in
theorem y_eq {Z Z' : w.Lt} (t : ColT w Z) (t' : ColT w Z') (u : B.Word) :
    (t'.C.forms u).to0.cls0.y = ((t.C.forms u).to0.cls0.y) :=
  funext fun c => Subtype.ext (((t'.std u).yE 0 (Nat.zero_le _) (Or.inl rfl) c).trans ((t.std u).yE 0 (Nat.zero_le _) (Or.inl rfl) c).symm)

set_option maxHeartbeats 4000000 in
theorem eY_eq {Z Z' : w.Lt} (t : ColT w Z) (t' : ColT w Z') (u : B.Word) :
    (t'.C.forms u).to0.val0.eY = ((t.C.forms u).to0.val0.eY) :=
  Equiv.ext fun c => Subtype.ext (((t'.std u).eY 0 (Nat.zero_le _) (Or.inl rfl) c).trans ((t.std u).eY 0 (Nat.zero_le _) (Or.inl rfl) c).symm)

set_option maxHeartbeats 4000000 in

theorem sameStd : SameStd := by
  intro B f T w Z Zn col col' F₁ h u
  have e : car (reL Z Zn) u (col'.C.forms u).to0.cls0.lev = car (reL Z Zn) u (F₁ u).cls0.lev :=
    (car_eq col col' u).trans ((congrArg (car Z u) (Eq.symm (h u).left)))
  have e2 := Sigma.ext_iff.1 (congrArg Prod.snd e)
  exact ⟨congrArg Prod.fst e, e2.1, e2.2, (y_eq col col' u).trans ((by with_unfolding_all exact ((h u).2.1.symm :))), (eY_eq col col' u).trans ((by with_unfolding_all exact ((h u).2.2.symm :)))⟩

end Std

section Mv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV Formalism.MainNotions Formalism.L2.Forms NumberField
  IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl Formalism.L2.SG.ColDict Formalism.L2.SG.HidaSetting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {F F' : ∀ u, Forms0 D u}

theorem SameCar_symm (h : SameCar F F') : SameCar F' F := fun u =>
  ⟨(h u).1.symm, (h u).2.1.symm, (h u).2.2.1.symm, (h u).2.2.2.1.symm, (h u).2.2.2.2.symm⟩

set_option maxHeartbeats 4000000 in

def trCar (h : SameCar F F') {X : HidaSetting D} {u} (t : Transport X u (F u)) : Transport X u (F' u) :=
  { t with
    hc_rep := fun c => by rw [(h u).2.2.2.1]; exact t.hc_rep c
    J_isom := fun c ξ η => by rw [(h u).2.2.2.2]; exact t.J_isom c ξ η }

set_option maxHeartbeats 4000000 in
theorem colDictL_car (h : SameCar F F') {X : HidaSetting D} {u} (t : Transport X u (F u)) (hK : X.LevelSubgroupCharacter) :
    colDictL X (trCar h t) hK = colDictL X t hK := by
  refine LinearMap.ext fun T => funext fun c => funext fun z => ?_
  exact congrArg (fun e => t.J (shP X u T.1 (t.hc c)) (e z)) (congrArg DFunLike.coe (h u).2.2.2.2)

theorem chi_of_heq {G : Type} [Group G] {U U' : Subgroup G} {chi : U →* ℂˣ} {chi' : U' →* ℂˣ} (e : U' = U) (h : HEq chi' chi)
    (x : G) (hx : x ∈ U') : chi' ⟨x, hx⟩ = chi ⟨x, e ▸ hx⟩ := by
  subst e
  rw [eq_of_heq h]

set_option maxHeartbeats 4000000 in
theorem lev_car (h : SameCar F F') {X : HidaSetting D} {u} {t : Transport X u (F u)} {hK : X.LevelSubgroupCharacter} (l : LevelMatch X t hK) :
    LevelMatch X (trCar h t) hK := by
  refine ⟨fun x => ?_, fun g y hr => ⟨?_, fun hk hy => ?_⟩⟩
  · rw [(h u).1]; exact l.1 x
  · rw [(h u).2.1]; exact (l.2 g y hr).1
  · rw [chi_of_heq (h u).2.1 (h u).2.2.1]; exact (l.2 g y hr).2 hk _

set_option maxHeartbeats 4000000 in

def packCar (h : SameCar F F') (P : SPack D F) : SPack D F' :=
  { P with
    tr := fun u => trCar h (P.tr u)
    into := fun u T => by rw [colDictL_car]; exact P.into u T
    bij := fun u => by unfold ColDictBij; rw [colDictL_car]; exact P.bij u
    lev := fun u => lev_car h (P.lev u)
    isom := fun u a b => by rw [colDictL_car]; exact P.isom u a b }

set_option maxHeartbeats 4000000 in

def restCar (h : SameCar F F') {P : SPack D F} (S : SRest P) : SRest (packCar h P) where
  hI := S.hI
  autTie := S.autTie
  colPin := fun u x => Subtype.ext ((LinearMap.congr_fun (colDictL_car h (P.tr u) P.Y.hK) _).trans (congrArg Subtype.val (S.colPin u x)))
  j := S.j
  rowPin := S.rowPin
  locTied := S.locTied

set_option maxHeartbeats 4000000 in

def satCar (h : SameCar F F') (p : RowPk D) (s : p.SAt F) : p.SAt F' :=
  { P := packCar h s.P, S := restCar h s.S, t := s.t, c := s.c, c_pos := s.c_pos, see := s.see, ev := s.ev, rowJ := s.rowJ }

end Mv

section Slot
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV Formalism.MainNotions Formalism.L2.Forms NumberField
  IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in

def SatMv : Prop := ∀ (B : Base) (C : Cols B) (a : Late B C) (p : RowPk a.D) (F0 : ∀ u, Forms0 a.D u)
  (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ) (F₁ : ∀ u, Forms0 (reL a (New.ofDiv a.D N hh)).D u),
  SameL a (New.ofDiv a.D N hh) F0 F₁ → p.SAt F0 → Nonempty (SAtL a (New.ofDiv a.D N hh) p.R p.F p.eE F₁)

set_option maxHeartbeats 8000000 in

theorem sxMv_of (H : SatMv) : SxMv := by
  intro K B f T w Z Wt p0 r col N h p0' t col' e ⟨s⟩
  obtain ⟨F₁, hF⟩ := exists_sameF_ofDiv (D := Late.D Z) ((N)) ((h)) fun u => (col.C.forms u).to0
  obtain ⟨s'⟩ := H B w.C Z (pkOf r) (fun u => (col.C.forms u).to0) ((N)) ((h)) ((F₁)) ((hF)) (cast (sx_eq r col) s)
  have c := sameStd B f T w Z (New.ofDiv (Late.D Z) ((N)) ((h))) col ((col')) ((F₁)) ((hF))
  have e' : pkOf t = (pkOf r).up Z Z.S N h := eq_of_heq e
  rw [sx_eq t col', e']
  exact ⟨satCar (D := Late.D (upL Z Z.S N h)) (F := (F₁)) ((c)) ((pkOf r).up Z Z.S N h) ((s'))⟩

theorem satMv : SatMv := fun B C a p F0 N hh F₁ hS s =>
  let ⟨s', _⟩ := sAtL_exists_ofDiv B C a p.G' p.Pl0 p.T p.A p.Ks p.R p.F F0 p.eE s N hh F₁ hS
  ⟨s'⟩

theorem sxMv : SxMv := sxMv_of satMv

set_option maxHeartbeats 4000000 in

theorem up_eE {B : Base} {C : Cols B} (a : Late B C) (S' : SStage B C a.W) (N : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V)
    (h : B.Word → ℝ) (p : RowPk a.D) : (p.up a S' N h).G' = p.G' ∧ (p.up a S' N h).Ks = p.Ks ∧ HEq (p.up a S' N h).eE p.eE :=
  ⟨rfl, rfl, (HEq.refl p.eE)⟩

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

set_option maxHeartbeats 4000000 in

theorem fam_up (Z : w.Lt) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (hX : B.fields.Ok)
    (U Xg tr) : famM (a := Z) (upL Z S' N h) (R3.famR (w.st Z) w.I hX U Xg tr).A = (R3.famR (w.st (upL Z S' N h)) w.I hX U Xg tr).A :=
  (Eq.refl (R3.famR (w.st (upL Z S' N h)) w.I hX U Xg tr).A)

set_option maxHeartbeats 4000000 in

theorem face_up (Z : w.Lt) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (hX : B.fields.Ok)
    (U Xg tr) : face (a := Z) (upL Z S' N h) (R3.face0 (w.st Z) w.I hX U Xg tr).lv2 =
      ((R3.face0 (w.st (upL Z S' N h)) w.I hX U Xg tr).lv2) := (Eq.refl (R3.face0 (w.st (upL Z S' N h)) w.I hX U Xg tr).lv2)

def fixH (𝒮 : Slots) (c : ℝ) : Slots :=
  { 𝒮 with Rx := fun K B f T w Z Wt p0 r => 𝒮.Rx K B f T w Z Wt p0 r × PLift (Z.V.div.h B.u₀ = c) }

set_option maxHeartbeats 4000000 in

theorem not_lv3Mv_fixH {𝒮 : Slots} {Z : w.Lt} (l : Lv3 𝒮 K w Z) : ¬ LevelThreeCondition (fixH 𝒮 (Z.V.div.h B.u₀)) := fun H => by
  obtain ⟨l', -⟩ := H K B f T w Z { l with rx := (l.rx, ⟨rfl⟩) } Z.S (fun u => (Z.V.div.Nu u).L) fun _ => Z.V.div.h B.u₀ + 1
  have : Z.V.div.h B.u₀ + 1 = Z.V.div.h B.u₀ := l'.rx.2.down
  linarith

end Slot

end GlobalTheory.Mem.SRe.CarModel

end
