import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ColDictValC
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ColDictValCPf

noncomputable section

open scoped Classical InnerProductSpace TensorProduct ComplexOrder
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.ColDict

namespace Formalism.L2.SG.Pf.ColDictPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev unitaryGroupFiniteAdeles (D : D7) : Subgroup (GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

abbrev unitaryGroupRational (D : D7) : Subgroup (GL (Fin (D.R.N 0)) D.host.E) :=
  Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))

abbrev bcA (D : D7) :
    GL (Fin (D.R.N 0)) D.host.E →* GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
  Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))

abbrev G0 (D : D7) : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ :=
  Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D)

instance instGroupUP0 (D : D7) : Group (unitaryGroupFiniteAdeles D) := Subgroup.toGroup _

set_option synthInstance.maxHeartbeats 200000

def RepFTot : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F)
    (h : Hfin X u), ∃ y : unitaryGroupFiniteAdeles D, RepF X Tr.wt Tr.ιA (h : X.B.I.Gf) y

def RepFOnto : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F)
    (y : unitaryGroupFiniteAdeles D), ∃ h : Hfin X u, RepF X Tr.wt Tr.ιA (h : X.B.I.Gf) y

def RepFUniq : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F)
    (h : X.B.I.Gf) (y y' : unitaryGroupFiniteAdeles D), RepF X Tr.wt Tr.ιA h y → RepF X Tr.wt Tr.ιA h y' → y = y'

def RepFInj : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F)
    (h h' : Hfin X u) (y : unitaryGroupFiniteAdeles D), RepF X Tr.wt Tr.ιA (h : X.B.I.Gf) y → RepF X Tr.wt Tr.ιA (h' : X.B.I.Gf) y → h = h'

def RepFRatF : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F)
    (γ : Gam X u), ∃ γ' ∈ unitaryGroupRational D, ∃ y : unitaryGroupFiniteAdeles D, (y : GL _ _) = bcA D γ' ∧
      RepF X Tr.wt Tr.ιA (iotaF X u γ : X.B.I.Gf) y

def RepFRatB : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F),
    ∀ γ' ∈ unitaryGroupRational D, ∃ γ : Gam X u, (∃ y : unitaryGroupFiniteAdeles D, (y : GL _ _) = bcA D γ' ∧
      RepF X Tr.wt Tr.ιA (iotaF X u γ : X.B.I.Gf) y) ∧
      ∀ τ, sTil X Tr.wt (iotaI X u γ : X.B.I.Ginf) τ =
        Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ

def HinfOnto : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F)
    (g : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ), (∀ τ, (g τ)ᴴ * G0 D τ * g τ = G0 D τ) →
    ∃ s ∈ Hinf X u, ∀ τ, sTil X Tr.wt s τ * g τ = 1

def GramDefiniteAtRealPlaces : Prop := ∀ (D : D7) (τ : D.what₂.Tau), (G0 D τ).PosDef ∨ (-G0 D τ).PosDef

structure TrFacts {D : D7} (X : HidaSetting D) {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u}
    (Tr : Transport X u F) : Prop where
  tot : ∀ h : Hfin X u, ∃ y : unitaryGroupFiniteAdeles D, RepF X Tr.wt Tr.ιA (h : X.B.I.Gf) y
  onto : ∀ y : unitaryGroupFiniteAdeles D, ∃ h : Hfin X u, RepF X Tr.wt Tr.ιA (h : X.B.I.Gf) y
  uniq : ∀ (h : X.B.I.Gf) (y y' : unitaryGroupFiniteAdeles D), RepF X Tr.wt Tr.ιA h y → RepF X Tr.wt Tr.ιA h y' → y = y'
  inj : ∀ (h h' : Hfin X u) (y : unitaryGroupFiniteAdeles D), RepF X Tr.wt Tr.ιA (h : X.B.I.Gf) y →
    RepF X Tr.wt Tr.ιA (h' : X.B.I.Gf) y → h = h'
  ratF : ∀ γ : Gam X u, ∃ γ' ∈ unitaryGroupRational D, ∃ y : unitaryGroupFiniteAdeles D, (y : GL _ _) = bcA D γ' ∧
      RepF X Tr.wt Tr.ιA (iotaF X u γ : X.B.I.Gf) y
  ratB : ∀ γ' ∈ unitaryGroupRational D, ∃ γ : Gam X u, (∃ y : unitaryGroupFiniteAdeles D, (y : GL _ _) = bcA D γ' ∧
      RepF X Tr.wt Tr.ιA (iotaF X u γ : X.B.I.Gf) y) ∧
      ∀ τ, sTil X Tr.wt (iotaI X u γ : X.B.I.Ginf) τ =
        Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ
  infOnto : ∀ g : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ, (∀ τ, (g τ)ᴴ * G0 D τ * g τ = G0 D τ) →
    ∃ s ∈ Hinf X u, ∀ τ, sTil X Tr.wt s τ * g τ = 1

section RepAlg

variable {D : D7} (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
  (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)

theorem repF_one : RepF X wt ιA 1 (1 : unitaryGroupFiniteAdeles D) := by
  intro j
  have e : X.B.I.fmat (1 : X.B.I.Gf) = 1 := by simp [AutInst.fmat]
  rw [e, Matrix.one_mulVec, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Matrix.one_apply, hb]
  · simp

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem repF_mul {h h' : X.B.I.Gf} {y y' : unitaryGroupFiniteAdeles D} (hy : RepF X wt ιA h y) (hy' : RepF X wt ιA h' y') :
    RepF X wt ιA (h * h') (y * y') := by
  intro j
  show X.B.I.fmat (h * h') *ᵥ qA X wt j = ∑ i, ιA.symm ((y.1.1 * y'.1.1) i j) • qA X wt i
  have hy2 : ∀ i, X.B.I.fmat h *ᵥ qA X wt i = ∑ k, ιA.symm (y.1.1 k i) • qA X wt k := hy
  have e1 : X.B.I.fmat (h * h') = X.B.I.fmat h * X.B.I.fmat h' := by simp [AutInst.fmat]
  rw [e1, ← Matrix.mulVec_mulVec, hy' j, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, hy2, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_smul, Matrix.mul_apply, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, mul_comm]

end RepAlg

section Phi

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u} {Tr : Transport X u F}
  (G : TrFacts X Tr)

def phi (h : Hfin X u) : unitaryGroupFiniteAdeles D := (G.tot h).choose

theorem phi_spec (h : Hfin X u) : RepF X Tr.wt Tr.ιA (h : X.B.I.Gf) (phi G h) := (G.tot h).choose_spec

theorem phi_eq {h : Hfin X u} {y : unitaryGroupFiniteAdeles D} (hy : RepF X Tr.wt Tr.ιA (h : X.B.I.Gf) y) : phi G h = y := G.uniq _ _ _ (phi_spec G h) hy

def phiHom : Hfin X u →* unitaryGroupFiniteAdeles D where
  toFun := phi G
  map_one' := phi_eq G (by exact repF_one X Tr.wt Tr.ιA)
  map_mul' a b := phi_eq G (by
    rw [Subgroup.coe_mul]
    exact repF_mul X Tr.wt Tr.ιA (phi_spec G a) (phi_spec G b))

def phiEq : Hfin X u ≃* unitaryGroupFiniteAdeles D :=
  MulEquiv.ofBijective (phiHom G)
    ⟨fun a b hab => G.inj a b (phi G a) (phi_spec G a) (by
        have : phi G a = phi G b := hab
        rw [this]; exact phi_spec G b),
     fun y => let ⟨h, hh⟩ := G.onto y; ⟨h, phi_eq G hh⟩⟩

end Phi

section Sharp

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter)

theorem piU_inner (s : Hinf X u) (a b : X.Vpi u) :
    ⟪X.piU u (s : X.B.I.Ginf) a, X.piU u (s : X.B.I.Ginf) b⟫_ℂ = ⟪a, b⟫_ℂ := (X.piU_rep u).2.2.1 _ (hinf_le_sinf X u _ s.2) a b

theorem piU_adj (s : Hinf X u) (a b : X.Vpi u) :
    ⟪X.piU u (s : X.B.I.Ginf) a, b⟫_ℂ = ⟪a, X.piU u ((s⁻¹ : Hinf X u) : X.B.I.Ginf) b⟫_ℂ := by
  have hs := hinf_le_sinf X u _ s.2
  have hs' := hinf_le_sinf X u _ (s⁻¹ : Hinf X u).2
  have hm := (X.piU_rep u).2.1 _ hs _ hs'
  have e : X.piU u (s : X.B.I.Ginf) (X.piU u ((s⁻¹ : Hinf X u) : X.B.I.Ginf) b) = b := by
    have h1 : (s : X.B.I.Ginf) * ((s⁻¹ : Hinf X u) : X.B.I.Ginf) = 1 := by simp
    rw [← ContinuousLinearMap.mul_apply, ← hm, h1, (X.piU_rep u).1, ContinuousLinearMap.one_apply]
  conv_lhs => rw [← e]
  exact (X.piU_rep u).2.2.1 _ hs _ _

theorem norm_psiK (κ : Ku X u hK) : ‖((psiK X u hK κ : ℂˣ) : ℂ)‖ = 1 := by
  show ‖X.chi2 ((X.xu u)⁻¹ * ((κ : Hfin X u) : X.B.I.Gf) * X.xu u)‖ = 1
  exact hK.2.2.2.2 _ κ.2

theorem rieszVector_rat (T : Cu X u hK) (γ : Gam X u) (h : Hfin X u) (κ : Ku X u hK) :
    shP X u T.1 (iotaF X u γ * h * (κ : Hfin X u)) =
      starRingEnd ℂ ((psiK X u hK κ : ℂˣ) : ℂ) • X.piU u (iotaI X u γ : X.B.I.Ginf) (shP X u T.1 h) := by
  obtain ⟨hT1, hT2⟩ := T.2
  have hsh : ∀ (g : Hfin X u) (ξ : X.Vpi u), ⟪shP X u T.1 g, ξ⟫_ℂ = T.1 ξ (1, g) := by
    intro g ξ
    simp [shP, InnerProductSpace.toDual_symm_apply]
  apply ext_inner_right ℂ
  intro ξ
  obtain ⟨hf1, hf2⟩ := hT1 ξ
  rw [hsh, inner_smul_left, Complex.conj_conj, piU_adj X u (iotaI X u γ), hsh]
  have e1 : ((1 : Hinf X u), iotaF X u γ * h * (κ : Hfin X u)) =
      ((1 : Hinf X u), iotaF X u γ * h) * (1, (κ : Hfin X u)) := by simp
  have e2 : ((1 : Hinf X u), iotaF X u γ * h) = (iotaI X u γ, iotaF X u γ) * ((iotaI X u γ)⁻¹, h) := by simp
  rw [e1, hf2, e2, hf1]
  rw [show T.1 (X.piU u (((iotaI X u γ)⁻¹ : Hinf X u) : X.B.I.Ginf) ξ) (1, h) =
      T.1 ξ ((1, h) * ((iotaI X u γ)⁻¹, 1)) from hT2 _ ξ _]
  simp

theorem rieszVector_rightTranslate (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (δ h : Hfin X u) :
    shP X u (rtr X δ T) h = shP X u T (h * δ) := by
  unfold shP
  congr 1
  ext ξ
  simp [rtr]

theorem reps_equiv {ι ι' : Type} (s : ι → Hfin X u) (s' : ι' → Hfin X u) (K : Subgroup (Hfin X u))
    (hs : ∀ h, ∃! i, ∃ (γ : Gam X u) (κ : K), h = iotaF X u γ * s i * (κ : Hfin X u))
    (hs' : ∀ h, ∃! i, ∃ (γ : Gam X u) (κ : K), h = iotaF X u γ * s' i * (κ : Hfin X u)) :
    ∃ e : ι ≃ ι', ∀ i, ∃ (γ : Gam X u) (κ : K), s i = iotaF X u γ * s' (e i) * (κ : Hfin X u) := by
  classical
  have inv_rel : ∀ (a b : Hfin X u) (γ : Gam X u) (κ : K), a = iotaF X u γ * b * (κ : Hfin X u) →
      b = iotaF X u γ⁻¹ * a * ((κ⁻¹ : K) : Hfin X u) := by
    intro a b γ κ h
    subst h
    simp [mul_assoc]
  let f : ι → ι' := fun i => (hs' (s i)).exists.choose
  let g : ι' → ι := fun i' => (hs (s' i')).exists.choose
  have hf : ∀ i, ∃ (γ : Gam X u) (κ : K), s i = iotaF X u γ * s' (f i) * (κ : Hfin X u) :=
    fun i => (hs' (s i)).exists.choose_spec
  have hg : ∀ i', ∃ (γ : Gam X u) (κ : K), s' i' = iotaF X u γ * s (g i') * (κ : Hfin X u) :=
    fun i' => (hs (s' i')).exists.choose_spec
  refine ⟨⟨f, g, fun i => ?_, fun i' => ?_⟩, hf⟩
  · obtain ⟨γ, κ, h⟩ := hf i
    exact (hs (s' (f i))).unique (hg (f i)) ⟨γ⁻¹, κ⁻¹, inv_rel _ _ _ _ h⟩
  · obtain ⟨γ, κ, h⟩ := hg i'
    exact (hs' (s (g i'))).unique (hf (g i')) ⟨γ⁻¹, κ⁻¹, inv_rel _ _ _ _ h⟩

theorem sum_reps {ι ι' : Type} [Fintype ι] [Fintype ι'] (s : ι → Hfin X u) (s' : ι' → Hfin X u)
    (K : Subgroup (Hfin X u))
    (hs : ∀ h, ∃! i, ∃ (γ : Gam X u) (κ : K), h = iotaF X u γ * s i * (κ : Hfin X u))
    (hs' : ∀ h, ∃! i, ∃ (γ : Gam X u) (κ : K), h = iotaF X u γ * s' i * (κ : Hfin X u))
    (Q : Hfin X u → ℂ) (hQ : ∀ (γ : Gam X u) (h : Hfin X u) (κ : K), Q (iotaF X u γ * h * (κ : Hfin X u)) = Q h) :
    ∑ i, Q (s i) = ∑ i', Q (s' i') := by
  obtain ⟨e, he⟩ := reps_equiv X u s s' K hs hs'
  calc ∑ i, Q (s i) = ∑ i, Q (s' (e i)) := Finset.sum_congr rfl fun i _ => by
          obtain ⟨γ, κ, h⟩ := he i
          rw [h, hQ]
    _ = ∑ i', Q (s' i') := Equiv.sum_comp e (fun i' => Q (s' i'))

theorem inner_shP_rat (T T' : Cu X u hK) (γ : Gam X u) (h : Hfin X u) (κ : Ku X u hK) :
    ⟪shP X u T'.1 (iotaF X u γ * h * (κ : Hfin X u)), shP X u T.1 (iotaF X u γ * h * (κ : Hfin X u))⟫_ℂ =
      ⟪shP X u T'.1 h, shP X u T.1 h⟫_ℂ := by
  rw [rieszVector_rat X u hK T γ h κ, rieszVector_rat X u hK T' γ h κ, inner_smul_left, inner_smul_right,
    piU_inner X u (iotaI X u γ), Complex.conj_conj, ← mul_assoc, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, norm_psiK X u hK κ]
  simp

end Sharp

section Adelic

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u} {Tr : Transport X u F}
  (G : TrFacts X Tr) {hK : X.LevelSubgroupCharacter} (hL : LevelMatch X Tr hK)

def gT (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) :
    unitaryGroupFiniteAdeles D → Formalism.L2.Forms.Fr D 0 (Nat.zero_le _) → ℂ :=
  fun x => Tr.J (shP X u T ((phiEq G).symm (x * Tr.h0⁻¹)))

def kUP (κ : F.cls0.lev.U) : unitaryGroupFiniteAdeles D :=
  ⟨κ.1, ((F.cls0.lev.U_eq κ.1).1 κ.2).1⟩

def levUP (Tr : Transport X u F) (κ : F.cls0.lev.U) : unitaryGroupFiniteAdeles D :=
  Tr.h0 * kUP κ * Tr.h0⁻¹

end Adelic

section Adelic2

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u} {Tr : Transport X u F}
  (G : TrFacts X Tr) {hK : X.LevelSubgroupCharacter} (hL : LevelMatch X Tr hK)

end Adelic2

section Onto

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u} {Tr : Transport X u F}
  (G : TrFacts X Tr)

theorem vpi_nontrivial (X : HidaSetting D) (u : D.what₂.Word) : Nontrivial (X.Vpi u) := by
  have hloc : ∀ v, ∃ x : X.Vloc u v, x ≠ 0 := fun v => by
    have := (X.piLoc_type u v).1
    exact exists_ne 0
  choose x hx using hloc
  refine ⟨⟨X.tensU u x, 0, fun h => ?_⟩⟩
  have h1 := X.tensU_inner u x x
  rw [h, inner_zero_left] at h1
  exact (Finset.prod_ne_zero_iff.2 (fun v _ => inner_self_ne_zero.2 (hx v))) h1.symm

end Onto

section Bij

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u} {Tr : Transport X u F}
  (G : TrFacts X Tr) {hK : X.LevelSubgroupCharacter} (hL : LevelMatch X Tr hK)

end Bij

section Isom

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u} {Tr : Transport X u F}
  (G : TrFacts X Tr) {hK : X.LevelSubgroupCharacter} (hL : LevelMatch X Tr hK)

end Isom

section Assembly

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u} {hK : X.LevelSubgroupCharacter}

end Assembly

end Formalism.L2.SG.Pf.ColDictPf

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.ColDictPf

end Formalism.L2.SG.Pf
