import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.LocalToGlobal.HermitianForms.TiedTwLv
import Formalism.LocalToGlobal.HermitianForms.DefsGH

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

def rSD (R : Ranks) : ℕ := R.m / 2 - 1

theorem rSym_rSD (R : Ranks) : rSym R.k (rSD R) = R.r := by
  unfold rSym rSD Ranks.r
  obtain ⟨j, hj⟩ := R.m_even
  have := R.two_le_m
  omega

theorem le_of_succ_m {R : Ranks} {i : ℕ} (h : i + 1 ≤ R.m) : i ≤ R.m := by omega

theorem succ_pred_m (R : Ranks) : R.m - 1 + 1 ≤ R.m := by
  have := R.two_le_m
  omega

variable {D : D7}

def FrExtFr (z0 : Fin (D.R.N D.R.m) → D.host.E) (G : GLoc D.host.F D.host.E (sigD D) D.host.g)
    (frm : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal →
      GL (Fin (D.R.N D.R.m)) (v.adicCompletion D.host.F))
    (frp : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal →
      GL (Fin (D.R.N D.R.m - 1)) (v.adicCompletion D.host.F)) : Prop :=
  ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal),
    (∀ (x : Fin (D.R.N D.R.m)) (b : Fin (D.R.N D.R.m - 1)) (b' : Fin (D.R.N D.R.m)), (b : ℕ) = b' →
      (frm i v h).1 x b' =
        ((iXm D).map ((G.phi i v h).comp (inclE (F := D.host.F) (v.adicCompletion D.host.F))) * (frp i v h).1) x b) ∧
    ∀ (x l : Fin (D.R.N D.R.m)), (l : ℕ) + 1 = D.R.N D.R.m →
      (frm i v h).1 x l = G.phi i v h (inclE (F := D.host.F) (v.adicCompletion D.host.F) (z0 x))

abbrev HSym (D : D7) (n : ℕ) (zl : Bool) (v : HeightOneSpectrum (𝓞 D.host.F)) : Subgroup (GL (Fin n) (kv D.host.F v)) :=
  JSymG (kv D.host.F v) n D.R.k (rSD D.R) D.R.t zl

set_option maxHeartbeats 4000000 in

structure FormsTiedSym (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) where
  atT : AtTTied u

  gl : GLoc D.host.F D.host.E (sigD D) D.host.g
  gl_K : ∀ i, (gl.piG i : D.host.E) ∈ D.host.K

  cls : ∀ i hi, (i = 0 ∨ i = D.R.m) → ClsTied u i hi
  val : ∀ i hi h, ValTied u atT.eV i hi (cls i hi h)

  glev0 : GLev (cls 0 (Nat.zero_le _) (Or.inl rfl)).lev gl D.R.k D.R.t 0 D.R.k (D.R.N 0) false

  lamM : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal →
    HSym D (D.R.N D.R.m) true v →* ℂˣ
  lamM_eq : ∀ a v h (M : HSym D (D.R.N D.R.m) true v), ((lamM a v h M : ℂˣ) : ℂ) =
    lamSym (gl.psi0 a v h) (gl.chiB a v h) D.R.k (rSD D.R) D.R.t D.R.m
      ((M : GL (Fin (D.R.N D.R.m)) (kv D.host.F v)) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) (kv D.host.F v))
  glevM : GLevH (cls D.R.m le_rfl (Or.inr rfl)).lev gl (fun _ v _ => HSym D (D.R.N D.R.m) true v) lamM
  lv : ∀ i hi, LvTied u atT i hi
  fMe : ∀ i hi h v, (cls i hi h).lev.fM (atT.eV v).1 (atT.eV v).2 ≃+ (D.mem u).A.Fv v
  fv : ∀ i hi h, FvTie (lv i hi) (cls i hi h) (fMe i hi h)
  upN : ∀ i hi h, UpNatTie (lv i hi) (cls i hi h) (val i hi h)
  dnN : ∀ i hi h, DnNatTie (lv i hi) (cls i hi h) (val i hi h)
  norm : ∀ i hi h, NormTie (val i hi h)
  bw : ∀ i hi h, BwTie atT (val i hi h)

  ch : ∀ i (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (β : Ch i),
    LevelChart D (D.mem u).A.T (badG D) i (le_of_succ_m h2)
      (fun c : {c // chOf i c = β} => (D.mem u).C.stab i c.1) (fun c => clsCrd D u i (le_of_succ_m h2) c.1)

  H : ∀ i (β : Ch i) (a : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal →
    Subgroup (GL (Fin (D.R.N i)) (kv D.host.F v))
  lamC : ∀ i β a v h, H i β a v h →* ℂˣ
  glevC : ∀ i h1 h2 β, GLevH (ch i h1 h2 β).lev gl (H i β) (lamC i β)
  eYC : ∀ i, 1 ≤ i → ∀ h2 : i + 1 ≤ D.R.m, (D.mem u).C.Y i ≃ Fr D i (le_of_succ_m h2)

  deC : ∀ i h1 h2, ∃ C : GL (Fin (D.R.N i)) D.host.E,
    cT (sigD D : D.host.E →+* D.host.E) C.1 * C.1 = gramN D i (le_of_succ_m h2) ∧
    (∀ x : Fin (D.R.N i) → D.host.E, x ∈ selfDualLatticeCoords D i (le_of_succ_m h2) ↔ ∀ a, (C.1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) ∧
    ∀ τ z, (D.mem u).C.de i z τ = embT D τ C.1.det * ((eYC i h1 h2 z).1 τ).det
  valC : ∀ i h1 h2, ValuationCompatibleChart (D.fm u) (eYC i h1 h2) (fun _ => True) (chOf i)
    (lat := fun c => clsCrd D u i (le_of_succ_m h2) c) (ch i h1 h2)
  ipVC : ∀ i h1 h2, IpVTieG (D.fm u) (eYC i h1 h2)
  normC : ∀ i h1 h2, NormTieG (D.fm u) (eYC i h1 h2)
  dilC : ∀ i h1 h2, DilationCompatibleChart (D.fm u) (eYC i h1 h2) atT.eV (chOf i)
    (lat := fun c => clsCrd D u i (le_of_succ_m h2) c) (ch i h1 h2)
  lvC : ∀ i (_ : 1 ≤ i) (h2 : i + 1 ≤ D.R.m),
    LevelCompatibleLattices (D.fm u) (D.mem u).A.T atT.res i (le_of_succ_m h2) (fun c => clsCrd D u i (le_of_succ_m h2) c)
  fMeC : ∀ i h1 h2 β v, (ch i h1 h2 β).lev.fM (atT.eV v).1 (atT.eV v).2 ≃+ (D.mem u).A.Fv v
  fvC : ∀ i h1 h2, FvTieG (lvC i h1 h2) atT.eV (ch i h1 h2) (fMeC i h1 h2)
  upC : ∀ i h1 h2, UpNatTieG (lvC i h1 h2) (eYC i h1 h2) atT.eV (ch i h1 h2)
  dnC : ∀ i h1 h2, DnNatTieG (lvC i h1 h2) (eYC i h1 h2) atT.eV (ch i h1 h2)
  bwC : ∀ i (_ : 1 ≤ i) (h2 : i + 1 ≤ D.R.m),
    BwTieG (D.fm u) (D.mem u).A.T atT.res (eYC i ‹_› h2) (fun c => clsCrd D u i (le_of_succ_m h2) c)

  levJ : StepLevel D.host.F D.host.E (sigD D) (gramN D (D.R.m - 1) (Nat.sub_le _ _)) (D.mem u).A.T D.R.f (badG D)
  lamJ : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal →
    HSym D (D.R.N (D.R.m - 1)) false v →* ℂˣ
  lamJ_eq : ∀ a v h (M : HSym D (D.R.N (D.R.m - 1)) false v), ((lamJ a v h M : ℂˣ) : ℂ) =
    lamSym (gl.psi0 a v h) (gl.chiB a v h) D.R.k (rSD D.R) D.R.t (D.R.m - 1)
      ((M : GL (Fin (D.R.N (D.R.m - 1))) (kv D.host.F v)) :
        Matrix (Fin (D.R.N (D.R.m - 1))) (Fin (D.R.N (D.R.m - 1))) (kv D.host.F v))
  glevJ : GLevH levJ gl (fun _ v _ => HSym D (D.R.N (D.R.m - 1)) false v) lamJ
  Yb : Type
  [YbFin : Finite Yb]
  [YbAct : MulAction levJ.U Yb]
  yb : Ch (D.R.m - 1) → Yb
  yb_orbit : ∀ y : Yb, ∃! β, ∃ κ : levJ.U, κ • yb β = y
  levJ_Lb : ∀ (h1 : 1 ≤ D.R.m - 1) β, (ch (D.R.m - 1) h1 (succ_pred_m D.R) β).lev.Lb = levJ.Lb
  levJ_le : ∀ (h1 : 1 ≤ D.R.m - 1) β, (ch (D.R.m - 1) h1 (succ_pred_m D.R) β).lev.U ≤ levJ.U
  levJ_stab : ∀ (h1 : 1 ≤ D.R.m - 1) β (κ : levJ.U),
    κ.1 ∈ (ch (D.R.m - 1) h1 (succ_pred_m D.R) β).lev.U ↔ κ • yb β = yb β
  levJ_chi : ∀ (h1 : 1 ≤ D.R.m - 1) β (κ : (ch (D.R.m - 1) h1 (succ_pred_m D.R) β).lev.U) (κ' : levJ.U), κ.1 = κ'.1 →
    (ch (D.R.m - 1) h1 (succ_pred_m D.R) β).lev.chi κ = levJ.chi κ'

  clsP : ClsPTied u
  valP : ValPTied u clsP
  normP : NormPTie valP
  lamP : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal →
    HSym D (D.R.N D.R.m - 1) false v →* ℂˣ
  eigenvalue_eq₂ : ∀ a v h (M : HSym D (D.R.N D.R.m - 1) false v), ((lamP a v h M : ℂˣ) : ℂ) =
    lamSym (gl.psi0 a v h) (gl.chiB a v h) D.R.k (rSD D.R) D.R.t D.R.m
      ((M : GL (Fin (D.R.N D.R.m - 1)) (kv D.host.F v)) :
        Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) (kv D.host.F v))
  glevP : GLevH clsP.lev gl (fun _ v _ => HSym D (D.R.N D.R.m - 1) false v) lamP
  til : TilTied u atT clsP (lv D.R.m le_rfl)
  tilLat : TilBaseLat til (cls D.R.m le_rfl (Or.inr rfl))
  tilFv : TilBaseFv til (cls D.R.m le_rfl (Or.inr rfl)) (fMe D.R.m le_rfl (Or.inr rfl))
  tilAd : TilAd til (cls D.R.m le_rfl (Or.inr rfl))
  frExt : FrExtFr til.z0 gl glevM.fr glevP.fr
  eWz : (D.mem u).P.Wz ≃ₗ[ℂ] ((D.fm u).clsP → (D.mem u).C.Y D.R.m → ℂ)
  evz : EvzTie tilAd (val D.R.m le_rfl (Or.inr rfl)) eWz
  jM : (D.mem u).P.Mt →ₛₗ[starRingEnd ℂ] (D.mem u).P.Wrow
  per : PerTie u jM

  DGam : (D.mem u).C.DGam = (D.mem D.u₀).C.DGam

attribute [instance] FormsTiedSym.YbFin FormsTiedSym.YbAct

theorem k_le_N (R : Ranks) (i : ℕ) : R.k ≤ R.N i := by
  unfold Ranks.N
  exact Nat.le_add_right _ _

abbrev HXS (D : D7) (i : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) : Subgroup (GL (Fin (D.R.N i)) (kv D.host.F v)) :=
  HX (kv D.host.F v) (D.R.N i) D.R.k (rSD D.R) D.R.t (D.R.m - 1 - i) (k_le_N D.R i)

set_option maxHeartbeats 4000000 in

structure OneLevelSymmetricForms (D : D7) (u : D.what₂.Word) extends FormsTiedSym D u (fun _ => Unit) (fun _ _ => ()) where
  H_eq : ∀ i (_ : 1 ≤ i) (_ : i + 2 ≤ D.R.m) a v hv, H i () a v hv = HXS D i v
  lamC_eq : ∀ i (_ : 1 ≤ i) (_ : i + 2 ≤ D.R.m) a v hv (M : H i () a v hv), ((lamC i () a v hv M : ℂˣ) : ℂ) =
    lamX (gl.psi0 a v hv) (gl.chiB a v hv) (D.R.N i) D.R.k (rSD D.R) D.R.t (D.R.m - 1 - i) i (k_le_N D.R i)
      ((M : GL (Fin (D.R.N i)) (kv D.host.F v)) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (kv D.host.F v))
  Yb_one : Subsingleton Yb

end Formalism.L2.Forms
