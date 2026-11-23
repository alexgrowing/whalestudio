import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.MtHeckeSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.EtaDet

open Formalism.L2.Col in

theorem prod_diag_inv {E : Type} [Field E] [NumberField E] [StarRing E] (n : ℕ) (π : 𝓞 E) (d : ℕ) (hd : d ≤ n) :
    ∏ i : Fin n, (mhlDiag n π d i)⁻¹ = (mhlA π)⁻¹ ^ d := by
  have h1 : ∀ i : Fin n, (mhlDiag n π d i)⁻¹ = (fun j : ℕ => if j < d then (mhlA π)⁻¹ else 1) i.1 := by
    intro i
    unfold mhlDiag
    by_cases h : i.1 < d <;> simp [h]
  rw [Finset.prod_congr rfl fun i _ => h1 i, Fin.prod_univ_eq_prod_range (fun j : ℕ => if j < d then (mhlA π)⁻¹ else 1) n,
    Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  have : (Finset.range n).filter (fun j => j < d) = Finset.range d := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.card_range]

theorem idem_mul_pow {R : Type} [CommRing R] {e : R} (hee : e * e = e) (x : R) (d : ℕ) : e * (e * x) ^ d = e * x ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, pow_succ, ← mul_assoc, ih]
    rw [show e * x ^ d * (e * x) = (e * e) * (x ^ d * x) by ring, hee]

theorem pow_mem_int {D : D7} {x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (d : ℕ) :
    x ^ d ∈ intAE D := by
  induction d with
  | zero => rw [pow_zero]; exact GlobalTheory.HeckeConj.one_mem_intAE D
  | succ d ih => rw [pow_succ]; exact GlobalTheory.HeckeConj.mul_mem_intAE D ih hx

theorem unit_mem {D : D7} {e a : Formalism.L2.Theta.AE D} (hee : e * e = e) (ha : finPart D (e * a) ∈ intAE D) (d : ℕ) :
    finPart D (e * a ^ d + (1 - e)) ∈ intAE D := by
  have he : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])
  rw [← idem_mul_pow hee a d, RingHom.map_add, RingHom.map_sub, RingHom.map_one, RingHom.map_mul, RingHom.map_pow]
  exact add_mem (GlobalTheory.HeckeConj.mul_mem_intAE D he (pow_mem_int ha d)) (sub_mem (GlobalTheory.HeckeConj.one_mem_intAE D) he)

theorem det_castGL {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (g : GL (Fin m) R) :
    Matrix.GeneralLinearGroup.det (castGL h g) = Matrix.GeneralLinearGroup.det g := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, castGL, Matrix.det_reindex_self]

theorem det_fin {D : D7} (V : HSp D) (α : GA D V) : finPart D (Formalism.L2.Theta.mt V α).det = (finHom V α).val.det := by
  rw [RingHom.map_det]; rfl

theorem det_swap {D : D7} {m : ℕ} (g : GL (Fin m) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) :
    swapAE D g.val.det = (Formalism.UG.bc (swapAE D) g).val.det := by
  rw [RingHom.map_det]; rfl

theorem det_cast {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (g : GL (Fin m) R) : (castGL h g).val.det = g.val.det := by
  have := congrArg Units.val (det_castGL h g)
  simpa only [Matrix.GeneralLinearGroup.val_det_apply] using this

theorem det_conj_inv {R : Type} [CommRing R] {n : ℕ} (C η : GL (Fin n) R) : ((C * η * C⁻¹)⁻¹).val.det = (η⁻¹).val.det := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.GeneralLinearGroup.val_det_apply]
  congr 1
  rw [map_inv, map_inv, map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]

theorem cast_inv {D : D7} (V : HSp D) {n : ℕ} (h : n = V.rank) (α : GA D V) :
    castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α⁻¹)) = (castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)))⁻¹ := by
  rw [map_inv (finHom V) α, map_inv (Formalism.UG.bc (swapAE D)), map_inv (castGL h.symm)]

end GlobalTheory.Mem.R3.LiftBrg.EtaDet

namespace GlobalTheory.Mem.R3.LiftBrg.EtaDet

theorem det_transport {D : D7} (V : HSp D) {n : ℕ} (h : n = V.rank) (α : GA D V) (C η : GL (Fin n) (Formalism.IndefR.Lev.EAf D))
    (hC : castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * η * C⁻¹) :
    swapAE D (finPart D (Formalism.L2.Theta.mt V α⁻¹).det) = (η⁻¹).val.det := by
  have hg : castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α⁻¹)) = (C * η * C⁻¹)⁻¹ := by
    rw [cast_inv V h α, hC]
  rw [det_fin V α⁻¹, det_swap (finHom V α⁻¹), ← det_cast h.symm (Formalism.UG.bc (swapAE D) (finHom V α⁻¹)), hg,
    det_conj_inv C η]

theorem prV_det_eta {D : D7} (n : ℕ) [NeZero n] (v : HeightOneSpectrum (𝓞 D.host.F)) {π : 𝓞 D.host.E} (hπ0 : π ≠ 0)
    (d : ℕ) :
    Formalism.UG.prV v ((((Formalism.L2.Col.mhlEta D.sp.cm n v hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) :
      GL (Fin n) (Formalism.IndefR.Lev.EAf D))⁻¹).val.det -
        Formalism.L2.Col.iA D.host.F D.host.E (∏ k : Fin n, (Formalism.L2.Col.mhlDiag n π d k)⁻¹)) = 0 := by
  have hdiag : ∀ i j : Fin n, Formalism.UG.prV v ((((Formalism.L2.Col.mhlEta D.sp.cm n v hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) :
      GL (Fin n) (Formalism.IndefR.Lev.EAf D))⁻¹).val i j) =
      Formalism.UG.prV v ((Matrix.diagonal fun k => Formalism.L2.Col.iA D.host.F D.host.E (Formalism.L2.Col.mhlDiag n π d k)⁻¹) i j) := by
    intro i j
    rw [Formalism.L2.Col.mhl_prV_eta_inv, Matrix.diagonal_apply]
    by_cases hij : i = j <;> simp [hij]
  have hm : (Formalism.UG.prV v).mapMatrix (((Formalism.L2.Col.mhlEta D.sp.cm n v hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) :
      GL (Fin n) (Formalism.IndefR.Lev.EAf D))⁻¹).val =
      (Formalism.UG.prV v).mapMatrix (Matrix.diagonal fun k => Formalism.L2.Col.iA D.host.F D.host.E (Formalism.L2.Col.mhlDiag n π d k)⁻¹) :=
    Matrix.ext hdiag
  rw [RingHom.map_sub, RingHom.map_det, hm, ← RingHom.map_det, Matrix.det_diagonal,
    map_prod (Formalism.L2.Col.iA D.host.F D.host.E), sub_self]

end GlobalTheory.Mem.R3.LiftBrg.EtaDet

namespace GlobalTheory.Mem.R3.LiftBrg.EtaDet

theorem hom_mul_pow {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a b : R) (d : ℕ) :
    f ((a * b) ^ d) = f a ^ d * f b ^ d := by
  rw [map_pow, map_mul, mul_pow]

theorem final_alg {R : Type} [CommRing R] {e Δ c X W : R} (hee : e * e = e) (key : e * Δ = e * c) (hc : c = X * W) :
    e * Δ = e * W * (e * X + (1 - e)) := by
  linear_combination key + e * hc + (W - W * X) * hee

theorem swap_inj {D : D7} {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (h : swapAE D x = swapAE D y) :
    x = y :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective h

theorem idem_eq_of_swap {D : D7} {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {x c : Formalism.L2.Theta.AE D}
    (h : swapAE D (finPart D e) * swapAE D (finPart D x) = swapAE D (finPart D e) * swapAE D (finPart D c)) :
    e * x = e * c := by
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · simp only [RingHom.map_mul, GlobalTheory.SplitScalar.infPart_splitIdem he, zero_mul]
  · apply swap_inj
    rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul]
    exact h

end GlobalTheory.Mem.R3.LiftBrg.EtaDet

namespace GlobalTheory.Mem.R3.LiftBrg.EtaDet

theorem det_clause : ∀ {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (e : Formalism.L2.Theta.AE D) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V), d ≤ n → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → (∀ z : Formalism.IndefR.Lev.EAf D, Formalism.UG.prV v z = 0 → swapAE D (finPart D e) * z = 0) → α ∈ GfC V → castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹ →
    ∃ u u' : Formalism.L2.Theta.AE D, finPart D u ∈ intAE D ∧ finPart D u' ∈ intAE D ∧ e * u * u' = e ∧
      e * (mt V α⁻¹).det = e * incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E) ^ d * u := by
  intro D V n _ h v Pb Ut d e C α hd he hε hα hC
  have hπ0 : ((Ut.π : 𝓞 D.host.E) : D.host.E) ≠ 0 := Formalism.L2.Col.mhl_alg_ne Ut.hπ0
  have hee : e * e = e := he.1.1
  have hfe : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])
  have hinv : finPart D (e * incA D ((Ut.π : D.host.E))⁻¹) ∈ intAE D := by
    by_contra hc
    exact Ut.hπP ((he.2 Ut.π Ut.hπ0).2 hc)
  have hpi : finPart D (e * incA D (Ut.π : D.host.E)) ∈ intAE D := by
    rw [RingHom.map_mul]
    exact GlobalTheory.HeckeConj.mul_mem_intAE D hfe (AddSubgroup.subset_closure ⟨1, fun v => one_mem _, Ut.π, rfl⟩)
  have hXY : incA D ((Ut.π : D.host.E))⁻¹ ^ d * incA D (Ut.π : D.host.E) ^ d = 1 := by
    rw [← mul_pow, ← RingHom.map_mul, inv_mul_cancel₀ hπ0, RingHom.map_one, one_pow]
  refine ⟨e * incA D ((Ut.π : D.host.E))⁻¹ ^ d + (1 - e), e * incA D (Ut.π : D.host.E) ^ d + (1 - e),
    unit_mem hee hinv d, unit_mem hee hpi d, ?_, ?_⟩
  · linear_combination e * hXY + ((e + 1) * (incA D ((Ut.π : D.host.E))⁻¹ ^ d * incA D (Ut.π : D.host.E) ^ d) -
      e * (incA D ((Ut.π : D.host.E))⁻¹ ^ d + incA D (Ut.π : D.host.E) ^ d) + (e - 1)) * hee
  ·
    have hdet := det_transport V h α C _ hC
    have hε' := hε _ (prV_det_eta (D := D) n v Ut.hπ0 d)
    rw [mul_sub, sub_eq_zero, prod_diag_inv n Ut.π d hd, Formalism.L2.Col.mhlA_inv Ut, ← hdet] at hε'
    have key : e * (Formalism.L2.Theta.mt V α⁻¹).det = e * incA D ((((Ut.π : D.host.E))⁻¹ *
        ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) ^ d) :=
      idem_eq_of_swap he.1 hε'
    have hc : incA D ((((Ut.π : D.host.E))⁻¹ * ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) ^ d) =
        incA D ((Ut.π : D.host.E))⁻¹ ^ d * incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E) ^ d :=
      hom_mul_pow (incA D) _ _ d
    exact final_alg hee key hc

end GlobalTheory.Mem.R3.LiftBrg.EtaDet
