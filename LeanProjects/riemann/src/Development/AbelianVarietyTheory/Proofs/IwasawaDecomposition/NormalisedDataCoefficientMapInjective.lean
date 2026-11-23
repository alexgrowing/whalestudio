import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCastMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelSame

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.Mem GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.RealGeo GlobalTheory.OneMapAll GlobalTheory.FieldBC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmExt

theorem heq_val {Γ W W' : Type} (n : NormedAddCommGroup W) (p : InnerProductSpace ℂ W) (n' : NormedAddCommGroup W')
    (p' : InnerProductSpace ℂ W') (hW : HEq W' W) (hn : HEq n' n) (hp : HEq p' p) (H : HMod (Γ → W)) (H' : HMod (Γ → W'))
    (hH : HEq H' H) (y : H.H) (y' : H'.H) (hy : HEq y' y) (g : Γ) : HEq (H'.e y' g) (H.e y g) ∧ HEq (0 : W') (0 : W) := by
  cases hW; cases hn; cases hp; cases hH; cases hy
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem heq_app {K V W W' : Type} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* ℂ}
    (n : NormedAddCommGroup W) (p : InnerProductSpace ℂ W) (n' : NormedAddCommGroup W') (p' : InnerProductSpace ℂ W')
    (hW : HEq W' W) (hn : HEq n' n) (hp : HEq p' p) (c' : V →ₛₗ[σ] W') (c : V →ₛₗ[σ] W) (h : HEq c' c) (v : V) :
    HEq (c' v) (c v) := by
  cases hW; cases hn; cases hp; cases h
  exact HEq.rfl

def RepsOver (D : D7) (i : Fin D.R.m) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (βV : ∀ i, GL (Fin (Vc D i).rank) (Lev.EAf D))
    {K' : Type} [Field K'] (bad : ℕ) {Cl : Type} (h : Cl → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i)))
    (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : K') : Prop :=
  bad ≠ 0 ∧ (∀ PP, PP ∈ Pg ∨ PP ∈ Q → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
    J' ≤ (levEnv (Vc D i) (βV i) (datY _ D.R.r D.R.t 1 (r_le_V i) Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.A)).J ∧
    J'.relIndex (levEnv (Vc D i) (βV i)
      (datY _ D.R.r D.R.t 1 (r_le_V i) Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.A)).J ≠ 0 ∧
    vol = ((J'.relIndex (levEnv (Vc D i) (βV i)
      (datY _ D.R.r D.R.t 1 (r_le_V i) Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.A)).J : ℕ) : K')⁻¹ ∧
    Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k)) ∧
    ∀ k, SplitOffBad (Vc D i) bad (h k) ∧ Lh k = Bridge.hLat (Vc D i) (fin _ (h k)) ∧
      gam k = Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) J' (fin _ (h k)))

theorem repsOver_cast {D : D7} {i : Fin D.R.m} {Pg₁ Pg₂ Q₁ Q₂ : Finset (Formalism.L2.DIV.Pl D.host.E)} {β₁ β₂} {K' : Type} [Field K'] {bad : ℕ}
    {Cl : Type} {h : Cl → GA D (Vc D i)} {J' Lh gam} {vol : K'} (hP : HEq Pg₂ Pg₁) (hQ₁ : Q₁ = ∅) (hQ₂ : Q₂ = ∅) (hβ : HEq β₂ β₁)
    (H : RepsOver D i Pg₁ Q₁ β₁ bad h J' Lh gam vol) : RepsOver D i Pg₂ Q₂ β₂ bad h J' Lh gam vol := by
  cases hP; cases hβ; subst hQ₁ hQ₂
  exact H

theorem inj_of_li {L K I W : Type} [Field L] [CharZero L] [Field K] [Fintype I] [AddCommGroup W] [Module ℂ W] {n : ℕ} (lam : I → DomWeight n)
    {σL : L →+* ℂ} {σK : K →+* ℂ} (jL : L →+* K) (s : Function.Surjective jL)
    {cL : VV L lam →ₛₗ[σL] W} {cK : VV K lam →ₛₗ[σK] W}
    (hc : ∀ v : VV L lam, ∃ v' : VV K lam, (v' : Pol K I n) = MvPolynomial.map jL (v : Pol L I n) ∧ cK v' = cL v)
    (hli : LinearIndependent ℂ fun i => cL (bVV L lam i)) : Function.Injective cK := by
  have hL : ∀ u : VV L lam, cL u = 0 → u = 0 := fun u hu => by
    have e := (bVV L lam).sum_repr u
    rw [← e, map_sum] at hu
    simp only [LinearMap.map_smulₛₗ] at hu
    have := Fintype.linearIndependent_iff.1 hli _ hu
    exact (bVV L lam).repr.injective (Finsupp.ext fun i => by
      rw [map_zero]; exact σL.injective ((this i).trans (map_zero _).symm))
  refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  let q := (RingEquiv.ofBijective jL ⟨jL.injective, s⟩).symm
  have h1 : jL.comp q.toRingHom = RingHom.id K := RingHom.ext fun x => (RingEquiv.ofBijective jL ⟨jL.injective, s⟩).apply_symm_apply x
  obtain ⟨a, a1, a2⟩ := hc ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV q.toRingHom lam _ v.2⟩
  have e : a = v := Subtype.ext (a1.trans (by rw [MvPolynomial.map_map, h1, MvPolynomial.map_id]))
  subst e
  have h0 := hL _ (a2.symm.trans hv)
  rw [h0] at a1
  exact Subtype.ext (a1.trans (map_zero _))

theorem normalisedData_coefficientMap_injective {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
    (O : OMDat C R i Unit (fun _ => A.μ0)) {κ v₀ ι x₀} (hOF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange)
    (hO : O.Pins κ v₀ ι x₀) : Function.Injective O.c0' := by
  have sj : Function.Surjective O.jL := fun y => by
    obtain ⟨x, hx⟩ := hOF.le y.2
    exact ⟨x, Subtype.ext ((RingHom.congr_fun hO.lift.field x).trans hx)⟩
  obtain ⟨g, r, c0L, hT, hbc⟩ := hO.lift.c0
  exact inj_of_li (lamV D i) O.jL sj hbc (hT.mapL i).2.1

set_option maxHeartbeats 4000000 in

theorem omOver_of_isBCOf (X X' : Stages) (hP : X'.B.toPre = X.B.toPre)
    {G : Type} [Group G] [Fintype G] {Pl0 T0 Pl0' T0' : Type} {A : FamIn X.toD7.what₂.LL G Pl0 T0 X.toD7.R.m}
    {A' : FamIn X'.toD7.what₂.LL G Pl0' T0' X'.toD7.R.m} (T : CoreJ X.toD7) [Algebra T.Q.c.F X.toD7.what₂.LL]
    (T' : CoreJ X'.toD7) [alg' : Algebra T'.Q.c.F X'.toD7.what₂.LL] (R : RealDat X.toD7 A T.Q.c.F) (R' : RealDat X'.toD7 A' T'.Q.c.F)
    (eH : HEq T'.Q.H T.Q.H) (el : HEq T'.Q.l T.Q.l) (ec : HEq T'.Q.c T.Q.c) (eD : HEq T'.Q.Dw T.Q.Dw) (eX : HEq T'.Q.Xo T.Q.Xo)
    (ePg : HEq R'.Pg R.Pg) (eβV : HEq R'.βV R.βV) (hL : R.toLevCh.Is A.μ0) (hL' : R'.toLevCh.Is A'.μ0)
    (i : Fin X.toD7.R.m) (i' : Fin X'.toD7.R.m) (hi : (i : ℕ) = i')
    (eW : HEq (R'.cV i').W (R.cV i).W) (en : HEq (R'.cV i').nW (R.cV i).nW) (ei : HEq (R'.cV i').iW (R.cV i).iW)
    (eHV : HEq (R'.HV i' A'.μ0) (R.HV i A.μ0))
    (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (O' : OMDat T'.toCore R' i' Unit (fun _ => A'.μ0))
    {κ ι x₀} {v₀ : (R.MW i (sg0 X.toD7 A)).Vec} {v₀' : (R'.MW i' (sg0 X'.toD7 A')).Vec} (hO : O.Pins κ v₀ ι x₀)
    (hinj : Function.Injective O.c0')
    (h : IsBCOf O' v₀' O v₀ κ ι x₀ (∀ x : A.fam.amb.FL i A.μ0, x = 0)) : GeoTies.OmOver O O' := by
  have hQ := GlobalTheory.RefPins.places_ref R hL
  have hQ' := GlobalTheory.RefPins.places_ref R' hL'
  obtain ⟨c₃, hs, c0₃, io₃, hw₃, h₀, J₀, hB, hS, hor, -⟩ := h
  obtain ⟨B', C', W', V', S', N', G'⟩ := X'
  rcases B' with ⟨P'⟩
  change P' = X.B.toPre at hP
  subst hP
  obtain ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V'', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := T'
  dsimp only at eH el ec eD eX
  obtain rfl := eq_of_heq eH
  obtain rfl := eq_of_heq el
  obtain rfl := eq_of_heq ec
  obtain rfl := eq_of_heq eD
  obtain rfl := eq_of_heq eX
  obtain rfl : i = i' := Fin.ext hi
  obtain @⟨c'', hle, jL, hV, c0', lev, dδ, Cl', fCl, bad, Lh, La, Nc, gam, vol, ep, BB, epF, io, hw, φ, w, U₂, dict₂, xi, thAd, Plc⟩ := O'
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, -, -, s15, -, -, s18, -, -, -⟩ := hS
  dsimp only [bc, merge] at s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s15 s18 hor
  obtain rfl := eq_of_heq s1
  subst s4
  subst s6
  obtain rfl := eq_of_heq s3
  obtain rfl := eq_of_heq s5
  obtain rfl := eq_of_heq s7
  obtain rfl := eq_of_heq s8
  obtain rfl := eq_of_heq s9
  obtain rfl := eq_of_heq s10
  obtain rfl := eq_of_heq s11
  obtain rfl := eq_of_heq s12
  obtain rfl := eq_of_heq s15
  obtain rfl := eq_of_heq s18
  refine ⟨s2, c'', hs, HEq.rfl, fun h J hr => ⟨(by with_unfolding_all exact (h :)), (by with_unfolding_all exact (J :)), ?_, fun x₀ x hx y' hy => ?_⟩⟩
  · exact (by with_unfolding_all exact ((repsOver_cast (D := X.toD7) (Pg₂ := R'.Pg) (Q₂ := R'.Q A'.μ0) (β₂ := (R'.βV)) ePg hQ hQ' ((eβV))
      (show RepsOver X.toD7 i R.Pg (R.Q A.μ0) R.βV _ h J _ _ _ from repsR_map (incF O.c' c'' hs) hr)) : _))
  · choose x' hx' using fun k => GlobalTheory.FieldBCModel.exists_over hs (lamV X.toD7 i) (x k)
    refine ⟨(by with_unfolding_all exact (x' :)), ?_, fun a n f hf hfx f' e => ?_⟩
    · intro k
      have hv := heq_val (Γ := Bridge.Gf (Vc X.toD7 i)) (R.cV i).nW (R.cV i).iW (R'.cV i).nW (R'.cV i).iW eW en ei (R.HV i A.μ0)
        ((by with_unfolding_all exact ((R'.HV i A'.μ0) :))) ((by with_unfolding_all exact (eHV :))) (jVx R i A.μ0 x₀) ((by with_unfolding_all exact (y' :))) ((by with_unfolding_all exact (hy :))) (fin _ (h k))
      rcases hor with hc | hp
      · have ha := heq_app (V := VsV X.toD7 i c''.F) (σ := inC c'') (R.cV i).nW (R.cV i).iW (R'.cV i).nW (R'.cV i).iW eW en ei
          ((by with_unfolding_all exact (c0' :))) c0₃ ((by with_unfolding_all exact (hc :))) (x' k)
        exact (by with_unfolding_all exact ((eq_of_heq (hv.1.trans ((heq_of_eq ((hx k).trans (hB.c0 _ _ (hx' k)).symm)).trans ha.symm))) :))
      · have h0 : (R.HV i A.μ0).e (jVx R i A.μ0 x₀) (fin _ (h k)) = 0 := by
          rw [hp x₀]
          unfold jVx
          rw [map_zero, map_zero]
          rfl
        have h1 : x k = 0 := hinj (((hx k).symm.trans h0).trans (map_zero _).symm)
        have h2 : x' k = 0 := Subtype.ext ((hx' k).trans (by rw [h1]; exact map_zero _))
        have h3 := eq_of_heq (hv.1.trans ((heq_of_eq h0).trans hv.2.symm))
        have h4 : ∀ c : VsV X.toD7 i c''.F →ₛₗ[inC c''] (R'.cV i).W, 0 = c (x' k) := fun c => by rw [h2, map_zero]
        exact (by with_unfolding_all exact ((h3.trans (h4 ((c0')))) : _))
    · obtain rfl := eq_of_heq e
      exact (by with_unfolding_all exact ((isThClsD_covBC_one hs (O.dδ ()) rfl _ _ _ _ _ _ O.io io x x' (fun k => hB.io _ _ (hx' k))
        (hO.cov ()).1.2.2.2.2.2.2.2.1 hf hfx) :))

end GlobalTheory.Mem.R3.Rw.OmExt
