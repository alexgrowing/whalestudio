import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.UnfoldingNonvanishingDoubleCosetHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemVGsOfMemQE

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def IsTw : Prop := ∀ a, I.cst a = twCst I.Ch I.sel (I.tup a) I.glob ∧
  I.idx a = twIdx I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 2)

@[reducible] def canon : TC B X :=
  { I with
    cst := fun a => twCst I.Ch I.sel (I.tup a) I.glob
    idx := fun a => twIdx I.Ch I.sel (I.tup a) (twCst I.Ch I.sel (I.tup a) I.glob) (B.R.m - 2) }

theorem canon_isTw : I.canon.IsTw := fun _ => ⟨rfl, rfl⟩

abbrev idxFull (a : I.ι) : ChIdx B.fields (B.primes X) B.R (I.Q a) :=
  (I.idx a).withTop (B.R.m - 2) (twLt I.Ch) (twTt I.sel (I.tup a))

def Deep : Prop := ∀ a (P : rowSG (B.primes X) I.sel (I.tup a)), P.1 ∉ (B.primes X).vGs → 2 * B.R.m ≤ (I.cst a).D P

variable {I}

theorem IsTw.cst_eq (h : I.IsTw) (a : I.ι) : I.cst a = twCst I.Ch I.sel (I.tup a) I.glob := (h a).1

theorem IsTw.idx_eq (h : I.IsTw) (a : I.ι) :
    I.idx a = twIdx I.Ch I.sel (I.tup a) (twCst I.Ch I.sel (I.tup a) I.glob) (B.R.m - 2) := by
  rw [(h a).2, (h a).1]

theorem IsTw.idxFull_eq (h : I.IsTw) (a : I.ι) :
    I.idxFull a = twIdxTop I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 2) (twLt I.Ch) (twTt I.sel (I.tup a)) := by
  unfold idxFull
  rw [(h a).2]
  rfl

theorem isTw_iff_canon_eq : I.IsTw ↔ I.canon = I := by
  refine ⟨fun h => ?_, fun h => h ▸ I.canon_isTw⟩
  have h1 : (fun a => twCst I.Ch I.sel (I.tup a) I.glob) = I.cst := funext fun a => (h.cst_eq a).symm
  have h2 : (fun a => twIdx I.Ch I.sel (I.tup a) (twCst I.Ch I.sel (I.tup a) I.glob) (B.R.m - 2)) = I.idx :=
    funext fun a => (h.idx_eq a).symm
  unfold canon
  rw [h2, h1]

theorem IsTw.deep (h : I.IsTw) : I.Deep := fun a P hP => by
  rw [h.cst_eq a, twCst_D_Q hP]

theorem qOf_mod_four (B : Base) (X : PreX B.toPre) : ∀ w ∈ (B.primes X).vGs, qOf w % 4 = 1 := fun w hw => by
  have hPr := (base_fields_primes_ok B X).2.1
  obtain ⟨k, hk⟩ : ∃ k, w ∈ (B.primes X).vG k := by
    classical
    unfold Primes.vGs at hw
    rcases Finset.mem_union.1 hw with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  rw [show qOf w = (B.primes X).g k from hPr.vG_norm k w hk]
  exact (hPr.g_cong k).of_dvd (by
    show 4 ∣ B.host.QS * B.host.q * B.host.d
    exact (((pow_dvd_pow 2 (Nat.le_add_left 2 B.R.e) : 2 ^ 2 ∣ 2 ^ (B.R.e + 2)).trans B.host.tower_dvd).mul_right _).mul_right _)

theorem val_of_ok (h : I.Ok) (j : Fin B.R.m) (w : HeightOneSpectrum (𝓞 B.fields.E)) (hw : w ∈ (B.primes X).vGs) :
    ∃ y : B.fields.K, I.glob.σ₀ y = ((((I.glob.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹ := by
  classical
  have hq : (qOf w : B.fields.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero w
  have e := (h.idx_ok I.mu0).muqG j j.2 ⟨w, Finset.mem_union_left _ hw⟩ hw (ciQU w) (by simp [ciQU, hq])
  refine ⟨(I.cst I.mu0).muq (j + 1) ⟨w, Finset.mem_union_left _ hw⟩ *
    (qValC (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) w : B.fields.Kˣ), ?_⟩
  rw [map_mul, e, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]

theorem Q_notMem_of_ok (h : I.Ok) (a : I.ι) : ∀ P ∈ I.Q a, P ∉ (B.primes X).vGs := fun _ hP =>
  IdxEx.notMem_vGs_of_mem_QE (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 h.sel_ok h.g_mem (I.tup a) hP

theorem degOne_of_ok (h : I.Ok) (a : I.ι) (P : rowSG (B.primes X) I.sel (I.tup a)) : TwDegOne B.fields P.1 :=
  degOneUnram_rowSG (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 h.sel_ok (I.tup a) P

theorem sqrt_of_ok (h : I.Ok) (a : I.ι) (P : rowSG (B.primes X) I.sel (I.tup a)) : ∃ z : B.fields.K, z ^ 2 = (qOf P.1 : B.fields.K) :=
  ⟨_, (h.idx_ok a).cst_ok.sq_sq P⟩

theorem root_of_ok (h : I.Ok) (hD : I.Deep) (a : I.ι) (P : rowSG (B.primes X) I.sel (I.tup a)) (hP : P.1 ∉ (B.primes X).vGs) :
    ∃ z : B.fields.K, I.glob.σ₀ z = Complex.exp (2 * Real.pi * Complex.I / ((qOf P.1 ^ (2 * B.R.m) : ℕ) : ℂ)) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hD a P hP)
  have hq : (qOf P.1 : B.fields.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
  have hqC : (qOf P.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.cast_ne_zero.1 hq)
  obtain ⟨x1, x2⟩ := (h.idx_ok a).xiUnitAtPrime P
  have hx : I.glob.xi0 ≠ 0 := fun e => x2 (e ▸ redP_zero)
  have hi : IntAt P.1 ((qOf P.1 ^ k : ℕ) : B.fields.E) := by
    simpa using GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int P.1 ((qOf P.1 ^ k : ℕ) : ℤ)
  have e := (h.idx_ok a).weil P (I.glob.xi0⁻¹ / (qOf P.1 : B.fields.E) ^ (2 * B.R.m)) ((qOf P.1 ^ k : ℕ) : ℤ)
    (by
      convert hi.mul (yIntAt_inv x1 x2) using 1
      rw [hk]; push_cast; field_simp; ring)
    (by
      convert GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int P.1 0 using 1
      rw [hk]; push_cast; field_simp; ring)
  refine ⟨_, e.trans ?_⟩
  congr 1
  rw [hk]; push_cast; field_simp; ring

theorem twIdx_ok_of_ok (h : I.Ok) (hD : I.Deep) (a : I.ι) :
    (twIdx I.Ch I.sel (I.tup a) (twCst I.Ch I.sel (I.tup a) I.glob) (B.R.m - 2)).Ok I.Ch I.sel (I.tup a)
      (twCst I.Ch I.sel (I.tup a) I.glob) I.glob (B.R.m - 2) :=
  twIdx_ok_closed (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 h.ch_ok (qOf_mod_four B X) I.glob
    h.ch_tied h.weil (val_of_ok h) h.hm (Q_notMem_of_ok h a) (fun P _ => degOne_of_ok h a P) (root_of_ok h hD a)
    (fun P _ => sqrt_of_ok h a P) (fun P _ => (h.idx_ok a).xiUnitAtPrime P)

theorem canon_ok (h : I.Ok) (hD : I.Deep) : I.canon.Ok :=
  { h with sharp := fun _ => rfl, idx_ok := twIdx_ok_of_ok (I := I) h hD }

theorem IsTw.chF_ok (ht : I.IsTw) (h : I.Ok) (W : Wts B.fields (B.primes X).Word B.R) (a : I.ι) (u : (B.primes X).Word) (j : ℕ) :
    (chF W I.sel (I.tup a) (I.idx a) u j).Ok := by
  have ho : ∀ b, ThetaOpen ((I.idx a).levQ j b) := by
    rw [(ht a).2]
    exact thetaOpen_twIdx I.Ch I.sel (I.tup a) (I.cst a) (h.idx_ok a).cst_ok (Q_notMem_of_ok h a) _ j
  exact chF_ok_of_finIdx W I.sel (I.tup a) _ (base_fields_primes_ok B X).1 u j
    (fun b P => thetaOpen_finIdx _ (ho b) P) (fun b c => thetaOpen_root _ (ho b) c)

theorem IsTw.chF_full_ok (ht : I.IsTw) (h : I.Ok) (W : Wts B.fields (B.primes X).Word B.R) (a : I.ι) (u : (B.primes X).Word) (j : ℕ) :
    (chF W I.sel (I.tup a) (I.idxFull a) u j).Ok := by
  rw [ht.idxFull_eq]
  exact twTop_chF_ok I.Ch I.sel (I.tup a) W (base_fields_primes_ok B X).1 (h.idx_ok a).cst_ok (Q_notMem_of_ok h a) _ u j

example (h : I.IsTw) (a : I.ι) : (I.cst a).sharp = true ∧ (I.cst a).M = B.R.m := by
  rw [h.cst_eq a]; exact ⟨rfl, rfl⟩

example (a : I.ι) (h : (I.cst a).sharp = false) : ¬ I.IsTw := fun ht => by
  rw [ht.cst_eq a] at h; exact Bool.noConfusion h

example : I.canon.C = I.C ∧ I.canon.xi = I.xi ∧ I.canon.glob = I.glob := ⟨rfl, rfl, rfl⟩

end GlobalTheory.Mem.Col2.TC

end
