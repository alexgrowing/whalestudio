import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValSubLtOfHasRes
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports

noncomputable section

namespace GlobalTheory.Mem.SRe.StdUnique

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Tr

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem pt_of_deco {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q Q' : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q' = ∅)
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} {p' : DecoF E n ST SG Q'} (e : p'.deco = p.deco)
    (h : IsPtOf hc g p) : IsPtOf hc g p' :=
  ⟨h.uni, e ▸ h.lat, e ▸ h.f, e ▸ h.be, fun P => (Finset.eq_empty_iff_forall_notMem.1 hQ P.1 P.2).elim⟩

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

set_option maxHeartbeats 2000000 in

theorem reads_mem (u : B.Word) (i : ℕ) {Lb Lb' : Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)}
    {U U' : Subgroup (GA B (B.R.N i))} {chi : U →* ℂˣ} {chi' : U' →* ℂˣ} {y : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)}
    {st st' : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E} {k k' : Unit → GA B (B.R.N i)}
    (hR : I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st k)
    (hR' : I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb') (fun _ => U') (fun _ => chi') y st' k')
    (x : U) (hx : x.1 ∈ UAd B.sp.cm (B.R.N i)) : ∃ h : x.1 ∈ U', chi' ⟨x.1, h⟩ = chi x := by
  obtain ⟨c, -⟩ := hR.onto ()
  obtain ⟨p0, hp0, -⟩ := hR.k_std ()
  have hk : k () ∈ UAd B.sp.cm (B.R.N i) := hp0.uni
  have hQ : QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have h1 : PtOf (y c * k ()) ((I.stp u I.mu0 i).rep c).1.1 := pt_of_deco hQ (extTo_deco _ _).symm (hR.pt c)
  have h2 : PtOf (y c * k' ()) ((I.stp u I.mu0 i).rep c).1.1 := pt_of_deco hQ (extTo_deco _ _).symm (hR'.pt c)
  have hyk : y c * k () ∈ UAd B.sp.cm (B.R.N i) := h1.uni
  have hg : y c * x.1 * k () ∈ UAd B.sp.cm (B.R.N i) := by
    have e : y c * x.1 * k () = (y c * k ()) * ((k ())⁻¹ * x.1 * k ()) := by group
    rw [e]
    exact mul_mem hyk (mul_mem (mul_mem (inv_mem hk) hx) hk)
  obtain ⟨q, hq⟩ := ChiFinTop.exists_isPtOf_of_mem (ST := (B.primes X).vT u) (SG := (B.primes X).vGs)
    (Q := QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K)) B.sp.cm hQ hg
  have hq' : PtOf (y c * x.1 * k' ()) q := by
    have e : y c * x.1 * k' () = y c * x.1 * k () * ((y c * k ())⁻¹ * (y c * k' ())) := by group
    rw [e]
    exact PtStab.isPtOf_mul_stab _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 hq
  obtain ⟨κ, hgam, hκq, hcos⟩ := (hR.lev c x.1 q hq).1 x.2
  have hm : x.1 ∈ U' := (hR'.lev c x.1 q hq').2 ⟨κ, hgam, hκq, hcos⟩
  refine ⟨hm, Units.ext ?_⟩
  exact (hR'.chr c ⟨x.1, hm⟩ κ hgam (by rw [hκq]; exact hq')).trans (hR.chr c x κ hgam (by rw [hκq]; exact hq)).symm

set_option maxHeartbeats 2000000 in

theorem reads_unique (u : B.Word) (i : ℕ) {Lb Lb' : Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)}
    {U U' : Subgroup (GA B (B.R.N i))} {chi : U →* ℂˣ} {chi' : U' →* ℂˣ} {y y' : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)}
    {st st' : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    (hR : ∃ k, I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st k)
    (hR' : ∃ k, I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb') (fun _ => U') (fun _ => chi') y' st' k) (hy : y' = y)
    (hU : U ≤ UAd B.sp.cm (B.R.N i)) (hU' : U' ≤ UAd B.sp.cm (B.R.N i)) : Lb' = Lb ∧ U' = U ∧ HEq chi' chi := by
  obtain ⟨k, hR⟩ := hR
  obtain ⟨k', hR'⟩ := hR'
  subst hy
  have e : U' = U := le_antisymm (fun x hx => (reads_mem I u i hR' hR ⟨x, hx⟩ (hU' hx)).1)
    fun x hx => (reads_mem I u i hR hR' ⟨x, hx⟩ (hU hx)).1
  subst e
  refine ⟨Submodule.ext fun x => (hR'.lb () x).trans (hR.lb () x).symm, rfl, heq_of_eq (MonoidHom.ext fun x => ?_)⟩
  exact (reads_mem I u i hR hR' x (hU x.2)).2

variable (l : I.Laws)

set_option maxHeartbeats 2000000 in

theorem lev_le (hI : I.Ok) (hP : TC.Pins B X) (Z : TC.Later B (I.cols l)) (u : B.Word) (i : ℕ) (hi : i ≤ B.R.m)
    (K : ClsTied (D := I.rec7 l Z) u i hi) : (show Subgroup (GA B (B.R.N i)) from K.lev.U) ≤ UAd B.sp.cm (B.R.N i) := by
  have hg1 : gramN (I.rec7 l Z) i hi = 1 := ((spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have eU : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      UAd B.sp.cm (B.R.N i) := by rw [hg1]; rfl
  exact fun x hx => eU ▸ ((K.lev.U_eq x).1 hx).1

set_option maxHeartbeats 4000000 in

theorem std_pair (hI : I.Ok) (hP : TC.Pins B X) (Z Z' : TC.Later B (I.cols l)) (u : B.Word) {Ch Ch' : ℕ → Type}
    {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} {chOf' : ∀ i, ((I.rec7 l Z').mem u).C.cls i → Ch' i}
    (F : FormsTiedSym (I.rec7 l Z) u Ch chOf) (F' : FormsTiedSym (I.rec7 l Z') u Ch' chOf')
    (hF : I.StdF l Z u F) (hF' : I.StdF l Z' u F') :
    F'.to0.cls0.lev.Lb = F.to0.cls0.lev.Lb ∧ F'.to0.cls0.lev.U = F.to0.cls0.lev.U ∧ HEq F'.to0.cls0.lev.chi F.to0.cls0.lev.chi ∧
      F'.to0.cls0.y = F.to0.cls0.y ∧ F'.to0.val0.eY = F.to0.val0.eY := by
  have hy : ∀ c : (I.stp u I.mu0 0).Cl, (F'.to0.cls0.y c).1 = (F.to0.cls0.y c).1 := fun c =>
    (hF'.yE 0 (Nat.zero_le _) (Or.inl rfl) c).trans (hF.yE 0 (Nat.zero_le _) (Or.inl rfl) c).symm
  have h := reads_unique I u 0 (hF.ends 0 (Nat.zero_le _) (Or.inl rfl)) (hF'.ends 0 (Nat.zero_le _) (Or.inl rfl)) (funext hy)
    (lev_le I l hI hP Z u 0 _ _) (lev_le I l hI hP Z' u 0 _ _)
  refine ⟨h.1, h.2.1, h.2.2, funext fun c => Subtype.ext (hy c), Equiv.ext fun z => Subtype.ext ?_⟩
  exact (hF'.eY 0 (Nat.zero_le _) (Or.inl rfl) z).trans (hF.eY 0 (Nat.zero_le _) (Or.inl rfl) z).symm

set_option maxHeartbeats 4000000 in

theorem car_of_same {D : D7} {u : D.what₂.Word} {F₁ F' : Forms0 D u}
    {lev : StepLevel D.host.F D.host.E (sigD D) (gramN D 0 (Nat.zero_le _)) (D.mem u).A.T D.R.f (badG D)}
    {y : (D.mem u).C.cls 0 → UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {eY : (D.mem u).C.Y 0 ≃ Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)}
    (h : F₁.cls0.lev = lev ∧ F₁.cls0.y = y ∧ F₁.val0.eY = eY)
    (h' : F'.cls0.lev.Lb = lev.Lb ∧ F'.cls0.lev.U = lev.U ∧ HEq F'.cls0.lev.chi lev.chi ∧ F'.cls0.y = y ∧ F'.val0.eY = eY) :
    F'.cls0.lev.Lb = F₁.cls0.lev.Lb ∧ F'.cls0.lev.U = F₁.cls0.lev.U ∧ HEq F'.cls0.lev.chi F₁.cls0.lev.chi ∧
      F'.cls0.y = F₁.cls0.y ∧ F'.val0.eY = F₁.val0.eY := by
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact h'

set_option maxHeartbeats 4000000 in

theorem sameStd : SameStd := by
  intro B f T w Z Zn col col' F₁ h u
  have h1 := std_pair w.I w.l w.ok w.pins Z (reL Z Zn) u (col.C.forms u) (col'.C.forms u) (col.std u) (col'.std u)
  exact car_of_same (F₁ := F₁ u) (F' := (col'.C.forms u).to0) (lev := (by with_unfolding_all exact ((col.C.forms u).to0.cls0.lev :)))
    (y := (by with_unfolding_all exact ((col.C.forms u).to0.cls0.y :))) (eY := (by with_unfolding_all exact ((col.C.forms u).to0.val0.eY :))) ((by with_unfolding_all exact ((h u) :))) ((by with_unfolding_all exact (h1 :)))

end GlobalTheory.Mem.SRe.StdUnique

end
