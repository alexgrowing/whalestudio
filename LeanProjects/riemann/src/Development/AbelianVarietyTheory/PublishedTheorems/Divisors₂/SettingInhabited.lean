import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange

noncomputable section

open WittVector Ideal CategoryTheory Opposite Function

namespace GlobalTheory.DieudonneTest

open PDivGroup Sandwich Dieudonne

theorem setting_inhabited (p : ℕ) [Fact p.Prime] :
    ∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : CharZero C) (v : Valuation C NNReal)
      (O : Type) (_ : CommRing O) (_ : Algebra O C) (_ : v.Integers O)
      (_ : Fact ¬IsUnit (p : O)) (_ : IsAdicComplete (span {(p : O)}) O) (ε : PreTilt O p),
      IsPrimitiveRoot (root ε).untilt p := by
  obtain ⟨h1, h2, ε, hv, hε⟩ := PadicComplexHost.main p
  exact ⟨ℂ_[p], inferInstance, inferInstance, inferInstance, Valued.v, _, inferInstance,
    inferInstance, hv, h1, h2, ε, hε⟩

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

theorem xi_dvd_of_eigen {ε : PreTilt O p} {a : Ainf p O}
    (h : WittVector.frobenius a = WittVector.frobenius (xi ε) * a) : xi ε ∣ a :=
  ⟨phiInv p O a, frobenius_injective (by rw [map_mul, frobenius_phiInv, h])⟩

open WittVector Ideal CategoryTheory Opposite Function in
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
private theorem exists_zmod_mul_of_pow_eq_pow_pred_mul {R : Type*} [CommRing R] [IsDomain R]
    {p : ℕ} [Fact p.Prime] [CharP R p] {t x : R} (ht : t ≠ 0)
    (hx : x ^ p = t ^ (p - 1) * x) : ∃ k : ZMod p, x = ZMod.castHom (dvd_refl p) R k * t := by
  classical
  by_contra hne
  push_neg at hne
  have hp : p.Prime := Fact.out
  set Q : Polynomial R := Polynomial.X ^ p - Polynomial.C (t ^ (p - 1)) * Polynomial.X with hQ
  have hdeg : Q.natDegree = p := by
    rw [hQ, Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
    rw [Polynomial.natDegree_X_pow]
    exact lt_of_le_of_lt ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)) hp.one_lt
  have hQ0 : Q ≠ 0 := fun h0 => by
    rw [h0, Polynomial.natDegree_zero] at hdeg
    exact hp.ne_zero hdeg.symm
  have hroot : ∀ y, y ^ p = t ^ (p - 1) * y → y ∈ Q.roots := fun y hy => by
    rw [Polynomial.mem_roots hQ0, Polynomial.IsRoot, hQ]
    simp [hy]
  set f : ZMod p → R := fun k => ZMod.castHom (dvd_refl p) R k * t with hf_def
  have hf : Function.Injective f := fun k l hkl =>
    ZMod.castHom_injective R (mul_right_cancel₀ ht hkl)
  have htp : t ^ p = t ^ (p - 1) * t := by rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
  have hfroot : ∀ k, f k ^ p = t ^ (p - 1) * f k := by
    intro k
    simp only [hf_def, mul_pow, ← map_pow, ZMod.pow_card, htp]
    ring
  have hsub : insert x (Finset.univ.image f) ⊆ Q.roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset]
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hroot _ hx
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hy
      exact hroot _ (hfroot k)
  have hnot : x ∉ Finset.univ.image f := fun hm => by
    obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hm
    exact hne k hk.symm
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hf, Finset.card_univ,
    ZMod.card] at hcard
  have h2 := (Multiset.toFinset_card_le Q.roots).trans (Polynomial.card_roots' Q)
  omega

open WittVector Ideal CategoryTheory Opposite Function in
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in

theorem _root_.GlobalTheory.DieudonneTest.eigen_step [IsDomain (PreTilt O p)] {ε : PreTilt O p}
    (hε : IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p) {a : _root_.GlobalTheory.Sandwich.Ainf p O}
    (h : WittVector.frobenius a = WittVector.frobenius (_root_.GlobalTheory.Sandwich.xi ε) * a) :
    ∃ (c : ℤ) (b : _root_.GlobalTheory.Sandwich.Ainf p O), a = c * _root_.GlobalTheory.Sandwich.mu ε + p * b ∧
      WittVector.frobenius b = WittVector.frobenius (_root_.GlobalTheory.Sandwich.xi ε) * b := by
  have hp : p.Prime := Fact.out
  have hrp : _root_.GlobalTheory.Sandwich.root ε ^ p = ε := by
    unfold _root_.GlobalTheory.Sandwich.root
    exact frobeniusEquiv_symm_pow_p (PreTilt O p) p ε
  have hε1 : ε ≠ 1 := by
    intro h1
    have hr1 : _root_.GlobalTheory.Sandwich.root ε = 1 := by
      unfold _root_.GlobalTheory.Sandwich.root
      rw [h1, map_one]
    rw [hr1, map_one] at hε
    have h2 := hε.eq_orderOf
    rw [orderOf_one] at h2
    exact hp.one_lt.ne' h2
  set t : PreTilt O p := ε - 1 with ht_def
  have ht : t ≠ 0 := sub_ne_zero.2 hε1
  set s : PreTilt O p := ∑ i ∈ Finset.range p, _root_.GlobalTheory.Sandwich.root ε ^ i with hs
  have hst : s ^ p * t = t ^ p := by
    have h1 : (_root_.GlobalTheory.Sandwich.root ε - 1) * s = t := by rw [hs, mul_geom_sum, hrp]
    have h2 : (_root_.GlobalTheory.Sandwich.root ε - 1) ^ p = t := by rw [sub_pow_char, one_pow, hrp]
    calc s ^ p * t = ((_root_.GlobalTheory.Sandwich.root ε - 1) * s) ^ p := by rw [mul_pow, h2, mul_comm]
      _ = t ^ p := by rw [h1]
  have hsp : s ^ p = t ^ (p - 1) := by
    apply mul_right_cancel₀ ht
    rw [hst, ← pow_succ, Nat.sub_add_cancel hp.one_le]
  have hξ0 : WittVector.coeff (_root_.GlobalTheory.Sandwich.xi ε) 0 = s := by
    rw [← WittVector.constantCoeff_apply]
    unfold _root_.GlobalTheory.Sandwich.xi
    simp [map_sum, map_pow, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, hs]
  have hμ0 : WittVector.coeff (_root_.GlobalTheory.Sandwich.mu ε) 0 = t := by
    unfold _root_.GlobalTheory.Sandwich.mu
    rw [← WittVector.constantCoeff_apply, map_sub, map_one, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero]
  have ha0 : WittVector.coeff a 0 ^ p = t ^ (p - 1) * WittVector.coeff a 0 := by
    have h3 := congrArg (fun x => WittVector.coeff x 0) h
    simp only [WittVector.mul_coeff_zero, WittVector.coeff_frobenius_charP, hξ0] at h3
    rw [h3, hsp]
  obtain ⟨k, hk⟩ := exists_zmod_mul_of_pow_eq_pow_pred_mul ht ha0
  refine ⟨(k.val : ℤ), ?_⟩
  set d : _root_.GlobalTheory.Sandwich.Ainf p O :=
    a - ((k.val : ℤ) : _root_.GlobalTheory.Sandwich.Ainf p O) * _root_.GlobalTheory.Sandwich.mu ε with hd
  have hd0 : WittVector.coeff d 0 = 0 := by
    rw [← WittVector.constantCoeff_apply, hd, map_sub, map_mul, map_intCast,
      WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, hμ0, hk]
    simp
  have hφd : WittVector.frobenius d = WittVector.frobenius (_root_.GlobalTheory.Sandwich.xi ε) * d := by
    rw [hd, map_sub, map_mul, map_intCast, h, _root_.GlobalTheory.Dieudonne.frobenius_mu]
    ring
  have hpd : ∃ b : _root_.GlobalTheory.Sandwich.Ainf p O, d = (p : _root_.GlobalTheory.Sandwich.Ainf p O) * b := by
    by_cases hd00 : d = 0
    · exact ⟨0, by rw [hd00, mul_zero]⟩
    obtain ⟨m, b, hb0, hmb⟩ := WittVector.exists_eq_pow_p_mul d hd00
    cases m with
    | zero =>
      rw [pow_zero, one_mul] at hmb
      rw [hmb] at hd0
      exact absurd hd0 hb0
    | succ m => exact ⟨(p : _root_.GlobalTheory.Sandwich.Ainf p O) ^ m * b, by rw [hmb, pow_succ']; ring⟩
  obtain ⟨b, hb⟩ := hpd
  refine ⟨b, by rw [← hb, hd]; ring, ?_⟩
  have hp0 : (p : _root_.GlobalTheory.Sandwich.Ainf p O) ≠ 0 := WittVector.p_nonzero p _
  apply mul_left_cancel₀ hp0
  have h4 := hφd
  rw [hb, map_mul, map_natCast] at h4
  rw [h4]
  ring

theorem eigen_approx [IsDomain (PreTilt O p)] {ε : PreTilt O p}
    (hε : IsPrimitiveRoot (root ε).untilt p) (n : ℕ) {a : Ainf p O}
    (h : WittVector.frobenius a = WittVector.frobenius (xi ε) * a) :
    ∃ c : ℤ, (p : Ainf p O) ^ n ∣ a - c * Sandwich.mu ε := by
  induction n generalizing a with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨c, b, rfl, hb⟩ := eigen_step hε h
    obtain ⟨d, e, he⟩ := ih hb
    refine ⟨c + p * d, e, ?_⟩
    rw [pow_succ', mul_assoc, ← he]
    push_cast
    ring

theorem finrank_add [IsDomain O] {ε : PreTilt O p} (h : CovariantDieudonneAt ε)
    (G : PDivGroup p O) :
    Module.finrank O G.dual.omega + Module.finrank O G.Lie = G.height := by
  obtain ⟨M, H, ψ, r, ι, π, -, -, -, -, -, -, hex, -, -, hf, -⟩ := h
  obtain ⟨⟨-, h2, h3⟩, -, -⟩ := hf G
  obtain ⟨hι, he, hπ⟩ := hex G
  have h4 := Submodule.finrank_quotient_add_finrank (LinearMap.ker (π G))
  rw [((π G).quotKerEquivOfSurjective hπ).finrank_eq, he.linearMap_ker_eq,
    LinearMap.finrank_range_of_inj hι, h3] at h4
  omega

theorem map_const_mu_mem {ε : PreTilt O p} (h : CovariantDieudonneAt ε) :
    ∃ M : PDivGroup p O ⥤ ModuleCat.{0} (Ainf p O),
      Module.finrank (Ainf p O) (M.obj (const p O)) = 1 ∧
      Module.finrank (Ainf p O) (M.obj (PDivGroup.mu p O)) = 1 ∧
      ∀ (f : const p O ⟶ PDivGroup.mu p O) (m : M.obj (const p O)),
        ∃ n, M.map f m = xi ε • n := by
  obtain ⟨M, H, ψ, r, ι, π, -, hM, -, -, hr, nr, hex, nι, nπ, -⟩ := h
  refine ⟨M, (hM _).2.2, (hM _).2.2, fun f m => ((hr _).2 _).1 ?_⟩
  rw [← nr]
  obtain ⟨w, hw⟩ := ((hex _).2.1 (r _ m)).1 (Subsingleton.elim _ _)
  rw [← hw, nι, Subsingleton.elim (omegaDualMap _ _ f w) 0, map_zero]

def trivialGroup : PDivGroup p O where
  height := 0
  A _ := O
  rank_eq n q := by
    have := q.nontrivial
    simp [Module.rankAtStalk_eq_finrank_of_free]
  res _ := BialgHom.id O O
  res_surjective _ := surjective_id
  ker_res n := le_antisymm (fun a ha => by rw [show a = 0 from ha]; exact zero_mem _)
    ((PDiv.kerIdeal_le_ker_iff _ (AlgHom.id O O)).2 fun a => by
      simpa using (PDiv.mulBy O O (p ^ n)).toAlgHom.commutes a)

theorem trivialGroup_id : 𝟙 (trivialGroup : PDivGroup p O) = 0 :=
  hom_ext fun n => BialgHom.ext fun a =>
    ((Hom.app (𝟙 (trivialGroup : PDivGroup p O)) n).toAlgHom.commutes a).trans
      ((Hom.app (0 : (trivialGroup : PDivGroup p O) ⟶ trivialGroup) n).toAlgHom.commutes a).symm

end GlobalTheory.DieudonneTest
