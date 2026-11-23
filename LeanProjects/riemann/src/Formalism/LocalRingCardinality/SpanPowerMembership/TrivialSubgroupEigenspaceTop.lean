import Formalism.LocalRingCardinality.SpanPowerMembership.EMjNApply

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.Inhab
open scoped TensorProduct

variable (D : D7) [hL : IsEmpty D.nd.Loc] (C : TwCore D.R D.host D.what₂ D.LL0 D.nd) (I : NzIn C)
  (he : ∀ g : G0g D.nd, D.what₂.embLL ((I.eL g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
  (E : EmbC D C) (S : StdMt D C I)

theorem trivialSubgroup_eigenspace_top {Γ K V : Type} [Group Γ] [Field K] [AddCommGroup V] [Module K V] (ψ : Γ →* Kˣ) :
    (⨅ u : (⊥ : Subgroup Γ), LinearMap.ker ((scalAct K V ψ u).toLinearMap -
      (((1 : (⊥ : Subgroup Γ) →* Kˣ) u : Kˣ) : K) • LinearMap.id)) = ⊤ := by
  refine iInf_eq_top.mpr fun u => LinearMap.ker_eq_top.mpr ?_
  have hu : u = 1 := Subsingleton.elim _ _
  subst hu
  rw [Subgroup.coe_one, map_one, map_one, Units.val_one, one_smul]
  exact sub_self _

set_option synthInstance.maxHeartbeats 400000 in
theorem nEG_one (i : C.Tw) (j : ℕ) (b : Bool) : NForms.eG (recN D C I he) i j b = 1 :=
  I.hPsi i b (I.ix j → FractionRing (C.O i))

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem nFm0_top (i : C.Tw) (j : ℕ) (b : Bool) : NForms.Fm0 (recN D C I he) i j b = ⊤ :=
  trivialSubgroup_eigenspace_top (Γ := G0g D.nd) (K := FractionRing (C.O i)) (V := I.ix j → FractionRing (C.O i)) (I.Psi i)

set_option synthInstance.maxHeartbeats 400000 in
theorem newformsBase_top (i : (recN D C I he).ntw.Tw) (j : ℕ) (b : Bool) : NForms.V0 (recN D C I he) i j b = ⊤ := by
  unfold NForms.V0
  rw [nEG_one D C I he i j b, nFm0_top D C I he i j b]
  exact Submodule.map_id _

set_option synthInstance.maxHeartbeats 400000 in
theorem nV0bc_top (i : (recN D C I he).ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) :
    ((NForms.V0 (recN D C I he) i j b).restrictScalars ((recN D C I he).ntw.O i)).baseChange
      ((recN D C I he).ntw.Ok i k) = ⊤ := by
  rw [newformsBase_top D C I he i j b, Submodule.restrictScalars_top, Submodule.baseChange_top]

variable (X : DivX (recN D C I he))

def mjH (j : ℕ) : HLat D.what₂.LL := X.MjH j

def jMD (j : ℕ) (y : (mjH D C I he X j).V) : D.what₂.Mj j := X.jM j y

structure StdMj where
  eI : ∀ j, I.ix j → (mjH D C I he X j).ι
  eI_bij : ∀ j, 1 ≤ j → j ≤ D.R.m → Function.Bijective (eI j)
  L_std : ∀ j, 1 ≤ j → j ≤ D.R.m →
    (mjH D C I he X j).L = Submodule.span (𝓞 D.what₂.LL) (Set.range (mjH D C I he X j).b)
  th_std : ∀ w j, 1 ≤ j → j ≤ D.R.m → ∀ (x : D.what₂.MtL (D.what₂.muTw w) j) (y : (mjH D C I he X j).V),
    jMD D C I he X j y = D.what₂.thetaP (D.what₂.muTw w) j (D.what₂.jMt (D.what₂.muTw w) j x) →
    ∀ a, (mjH D C I he X j).b.repr y (eI j a) = (S.bT w j).repr x (I.rM j a)

variable (T : StdMj D C I he S X)

theorem eMjN_th (w : D.what₂.places.Pl) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (x : D.what₂.MtL (D.what₂.muTw w) j) (y : (mjH D C I he X j).V)
    (hy : jMD D C I he X j y = D.what₂.thetaP (D.what₂.muTw w) j (D.what₂.jMt (D.what₂.muTw w) j x)) :
    eMjN D C I E (mjH D C I he X j) w j (T.eI j) y =
      vE D C I E w j (LinearMap.funLeft (C.Ok (E.twI w) 1) (FractionRing (C.Ok (E.twI w) 1)) (I.rM j)
        (eMtN D C I E S w j x)) := by
  rw [eMjN_apply]
  congr 1
  funext a
  exact congrArg (E.embW w) (T.th_std w j h1 h2 x y hy a)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

def nmjN : NMj (recN D C I he) X (nchN D C I he E S) where
  eMj := fun w j => eMjN D C I E (mjH D C I he X j) w j (T.eI j)
  eMj_smul := fun w j a r x h => eMjN_smul D C I E (mjH D C I he X j) w j (T.eI j) a r x h
  eMj_li := fun w j _ h1 h2 => eMjN_li D C I E (mjH D C I he X j) w j (T.eI j) (T.eI_bij j h1 h2)
  eMj_lat := fun w j _ h1 h2 => by
    have h := sv_lat D C I E w j
    rw [← eMjN_span D C I E (mjH D C I he X j) w j (T.eI j) (T.eI_bij j h1 h2) (T.L_std j h1 h2)] at h
    have e2 := nV0bc_top D C I he (E.twI w) j true 1
    exact e2.symm ▸ h
  eMj_th := fun w j _ h1 h2 x _ y hy => by
    have h := eMjN_th D C I he E S X T w j h1 h2 x y hy
    have h4 := NChoice.thPe_one (recN D C I he) (nchN D C I he E S) w j (eMtN D C I E S w j x)
    have h6 := NChoice.fracEquiv_symm (K := C.Ok (E.twI w) 1) (eMtN D C I E S w j x)
    exact (congrArg (NChoice.toFracE _ _ w j) h).trans
      (h4.symm.trans (congrArg (NChoice.thPe (recN D C I he) (nchN D C I he E S) w j) h6.symm))

end Formalism.BasicNotions.Examples₂.NZ
