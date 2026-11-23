import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralDivUniformizerOfRedZero

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.Col2.LevMod

open GlobalTheory.CongLevel

section Red

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))

def RedTo (g : Sp E n ≃ₗ[E] Sp E n) (hbar : GL (Fin n) (𝓞 E ⧸ P.asIdeal)) : Prop :=
  ∀ x ∈ stdAt E n P, redV P (g x) = hbar.1.mulVec (redV P x)

variable {P}

theorem RedTo.one : RedTo P (1 : Sp E n ≃ₗ[E] Sp E n) 1 := fun x _ => by
  rw [Units.val_one, Matrix.one_mulVec]; rfl

theorem RedTo.mul {g g' : Sp E n ≃ₗ[E] Sp E n} {a b : GL (Fin n) (𝓞 E ⧸ P.asIdeal)} (hg' : g' ∈ GLint E n P)
    (h : RedTo P g a) (h' : RedTo P g' b) : RedTo P (g * g') (a * b) := fun x hx => by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← h' x hx]
  exact h _ ((hg' x).2 hx)

theorem RedTo.inv {g : Sp E n ≃ₗ[E] Sp E n} {a : GL (Fin n) (𝓞 E ⧸ P.asIdeal)} (hg : g ∈ GLint E n P)
    (h : RedTo P g a) : RedTo P g⁻¹ a⁻¹ := fun x hx => by
  have h1 := h _ (((inv_mem hg : g⁻¹ ∈ GLint E n P) x).2 hx)
  rw [show g (g⁻¹ x) = x from g.apply_symm_apply x] at h1
  rw [h1, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

variable (P) in

def redSub (G : Subgroup (Sp E n ≃ₗ[E] Sp E n)) (hG : G ≤ GLint E n P) : Subgroup (GL (Fin n) (𝓞 E ⧸ P.asIdeal)) where
  carrier := {a | ∃ g ∈ G, RedTo P g a}
  one_mem' := ⟨1, one_mem _, RedTo.one⟩
  mul_mem' := fun ⟨g, hg, h⟩ ⟨g', hg', h'⟩ => ⟨g * g', mul_mem hg hg', RedTo.mul (hG hg') h h'⟩
  inv_mem' := fun ⟨g, hg, h⟩ => ⟨g⁻¹, inv_mem hg, h.inv (hG hg)⟩

end Red

theorem unipotentArg_extendByIdOnLastCoords {E : Type} [Field E] {n : ℕ} (c : ℕ) (κ : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    Loc.n1Arg (extE c κ) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [add_assoc, extE_apply, resX_eN]
  simp only [map_zero, sub_self, add_zero]
  unfold Loc.atN Loc.eN
  split_ifs with h1 h2
  · exact absurd h2 (by simp)
  · rfl
  · rfl

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem extE_mem_Cbe (sharp : Bool) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.E)) (hw : w ∈ Pr.vGs)
    (hd : ∀ a : X.E, IntAt w a → redP w a = 0 → IntAt w (a / (qOf w : X.E))) (h : AutY X R j)
    (hh : h ∈ stabL X.E _ (lamYat (Pr := Pr) j w)) (κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j))
    (hκ : κ ∈ GLint X.E (R.N j) w) (hr : ∀ x ∈ stdAt X.E (R.N j) w, redV w (κ x) = redV w x) :
    extE (cOf R j) κ ∈ Loc.Cbe (Jat (Pr := Pr) sharp j w) h := by
  have hq : ((qOf w : ℕ) : X.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero w
  unfold lamYat at hh
  rw [if_pos hw] at hh
  refine ⟨extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ κ, ?_⟩
  have e : (MulAut.conj h⁻¹).toMonoidHom (extE (cOf R j) κ) = h⁻¹ * extE (cOf R j) κ * h := by simp
  show (MulAut.conj h⁻¹).toMonoidHom (extE (cOf R j) κ) ∈ Jat (Pr := Pr) sharp j w
  rw [e]
  have hs := mul_mem (mul_mem (inv_mem hh) (extE_stab w (qOf w) (cOf R j) (fun i => i + 1) κ hκ)) hh
  have hc := conj_cong (qOf w) _ _ h hh (extE_cong w (qOf w) (cOf R j) (fun i => i + 1) hd κ hκ hr)
  unfold Jat
  rw [if_pos hw]
  split_ifs
  · refine ⟨hs, mem_flagU (qOf w) _ _ _ _ _ (fun s => ?_) (fun s x hx => ?_) (fun s => ?_) _ hs hc⟩
    · exact CongLevel.sclLat_le w _ hq _ _ _
    · exact smul_mem_sclLat w _ hq _ _ _ x hx
    · exact bvec_mem w _ hq _ _ _
  · refine ⟨hs, mem_flagU (qOf w) _ _ _ _ _ (fun s => ?_) (fun s x hx => ?_) (fun s => ?_) _ hs hc⟩
    · exact CongLevel.sclLat_le w _ hq _ _ _
    · exact smul_mem_sclLat w _ hq _ _ _ x hx
    · exact bvec_mem w _ hq _ _ _

theorem exists_levG : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j), cst.Ok → P.1 ∈ Pr.vGs → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1) → prCat (Pr := Pr) cst.sharp j P.1 h ≤ GLint X.E (R.N j) P.1 → (∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P.1, y x ∈ lamYat (Pr := Pr) (R := R) j P.1) → lamRow Ch mu cst.sharp j P.1 (LinearMap.id + (qOf P.1 : X.E) • y) = 1) → ChiMul Ch sel mu cst j P h → ChiTriv Ch sel mu cst j P h → ∃ lev : Lev (𝓞 X.E ⧸ P.1.asIdeal) X.K (R.N j), GrpG sel mu cst j P h lev ∧ ChrG Ch sel mu cst j P h lev := by
  intro X Pr R Ch sel S mu cst j P h hc hP hdu hh hle hlam hmul htriv
  have hq : ((qOf P.1 : ℕ) : X.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
  have hd : ∀ a : X.E, IntAt P.1 a → redP P.1 a = 0 → IntAt P.1 (a / (qOf P.1 : X.E)) := fun a ha h0 => by
    have := GlobalTheory.TypePrimeUnif.intAt_div_of_notMem_sq P.1 _ (Ideal.absNorm_mem _) hdu.2 a ha h0
    rwa [map_natCast] at this
  have hone : ∀ κ ∈ GLint X.E (R.N j) P.1, (∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (κ x) = redV P.1 x) →
      chiInv Ch sel mu cst j P h (extE (cOf R j) κ) = 1 := by
    intro κ hκ hr
    unfold lamYat at hh hlam
    rw [if_pos hP] at hh hlam
    have hcong := conj_cong (qOf P.1) _ _ h hh
      (extE_cong P.1 (qOf P.1) (cOf R j) (fun i => i + 1) hd κ hκ hr)
    have h1 := hlam ((qOf P.1 : X.E)⁻¹ • ((h⁻¹ * extE (cOf R j) κ * h : AutY X R j).toLinearMap - LinearMap.id))
      fun x hx => by
        have h2 := hcong x hx
        rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
        exact h2
    rw [smul_inv_smul₀ hq, add_sub_cancel] at h1
    unfold chiInv
    rw [h1, unipotentArg_extendByIdOnLastCoords, hc.psi_int P 0 (by simpa using CongLevel.intAt_nat P.1 0), inv_one, one_mul]
  obtain ⟨lam, hl⟩ := exists_char (H := ↥(redSub P.1 _ hle)) (CAt sel mu cst j P h) (chiInv Ch sel mu cst j P h)
    (fun r a => ∃ g ∈ GLint X.E (R.N j) P.1,
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g x)) ∧ RedTo P.1 g a.1)
    hmul.1 hmul.2
    (fun ⟨a, g, hg, hga⟩ => by
      obtain ⟨r, hr, hrg⟩ := id hg
      exact ⟨r, hr, g, hle hg, hrg, hga⟩)
    (by
      rintro r a r' a' ⟨g, hg, h1, h2⟩ ⟨g', hg', h1', h2'⟩
      refine ⟨g * g', mul_mem hg hg', fun x => ?_, RedTo.mul hg' h2 h2'⟩
      show r (r' _) = _
      rw [h1', h1]
      rfl)
    (by
      rintro a r hr r' hr' ⟨g, hg, h1, h2⟩ ⟨g', hg', h1', h2'⟩
      have hκ : g⁻¹ * g' ∈ GLint X.E (R.N j) P.1 := mul_mem (inv_mem hg) hg'
      have hred : ∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 ((g⁻¹ * g') x) = redV P.1 x := fun x hx => by
        rw [RedTo.mul hg' (h2.inv hg) h2' x hx, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      have hs : extE (cOf R j) (g⁻¹ * g') ∈ CAt sel mu cst j P h := extE_mem_Cbe _ j P.1 hP hd h hh _ hκ hred
      have ht : (extE (cOf R j) (g⁻¹ * g'))⁻¹ * (r⁻¹ * r') ∈ CAt sel mu cst j P h :=
        mul_mem (inv_mem hs) (mul_mem (inv_mem hr) hr')
      have ht1 := htriv _ ht fun x => by
        show (extE (cOf R j) (g⁻¹ * g')).symm (r.symm (r' _)) = _
        rw [LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_eq, extE_inX, h1, h1']
        exact congrArg _ (g.apply_symm_apply _).symm
      have e : r' = r * (extE (cOf R j) (g⁻¹ * g') * ((extE (cOf R j) (g⁻¹ * g'))⁻¹ * (r⁻¹ * r'))) := by
        rw [mul_inv_cancel_left, mul_inv_cancel_left]
      have h3 := hmul.2 r hr _ (mul_mem hs ht)
      rw [← e, hmul.2 _ hs _ ht, ht1, hone _ hκ hred, mul_one, mul_one] at h3
      exact h3.symm)
  exact ⟨⟨redSub P.1 _ hle, lam⟩, fun _ => Iff.rfl,
    fun a g r hr h1 h2 => hl a r hr ⟨g, hle ⟨r, hr, h1⟩, h1, h2⟩⟩

end GlobalTheory.Mem.Col2.LevMod

end
