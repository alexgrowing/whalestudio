import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfCompEqSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfThetaPhiInv

set_option autoImplicit false

noncomputable section

open CategoryTheory WittVector
open scoped TensorProduct Pointwise ChangeOfRings

namespace GlobalTheory.RingChain.RingMap

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published GlobalTheory.PerfdLat

section Tilt

variable {O O' : Type} [CommRing O] [CommRing O'] (p : ℕ) [Fact p.Prime] [Fact ¬IsUnit (p : O)] [Fact ¬IsUnit (p : O')]

def tiltHom (σ : O →+* O') : PreTilt O p →+* PreTilt O' p :=
  Perfection.map p (R := ModP O p) (S := ModP O' p) (Ideal.quotientMap (Ideal.span {(p : O')}) σ (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.subset_span rfl))

theorem coeff_tiltHom (σ : O →+* O') (x : PreTilt O p) (n : ℕ) (y : O)
    (h : PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {(p : O)}) y) :
    PreTilt.coeff n (tiltHom p σ x) = Ideal.Quotient.mk (Ideal.span {(p : O')}) (σ y) :=
  (congrArg (fun z => Ideal.quotientMap (Ideal.span {(p : O')}) σ (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.subset_span rfl) z) h :)

variable [IsAdicComplete (Ideal.span {(p : O)}) O] [IsAdicComplete (Ideal.span {(p : O')}) O']

theorem untilt_tiltHom (σ : O →+* O') (x : PreTilt O p) : (tiltHom p σ x).untilt = σ x.untilt := by
  refine Perfection.teichmuller_spec (I := Ideal.span {(p : O')}) fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {(p : O)}) (PreTilt.coeff n x)
  refine ⟨σ y, (coeff_tiltHom p σ x n y hy.symm).symm, ?_⟩
  have h1 := (Perfection.teichmuller_sModEq (I := Ideal.span {(p : O)}) (x := x) hy).symm
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1 ⊢
  have h2 := map_dvd σ h1
  rw [map_pow, map_natCast, map_sub, map_pow] at h2
  exact h2

theorem fontaineTheta_tiltHom (σ : O →+* O') (a : Ainf p O) :
    fontaineTheta O' p (WittVector.map (tiltHom p σ) a) = σ (fontaineTheta O p a) := by
  refine (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : O')})).2 fun n => ?_
  rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, ← Ideal.Quotient.eq]
  have key := WittVector.eq_of_apply_teichmuller_eq
    ((Ideal.Quotient.mk (Ideal.span {(p : O')} ^ n)).comp ((fontaineTheta O' p).comp (WittVector.map (tiltHom p σ))))
    ((Ideal.Quotient.mk (Ideal.span {(p : O')} ^ n)).comp (σ.comp (fontaineTheta O p)))
    ⟨n, by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : O')} ^ n)), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n⟩
    (fun x => by simp only [RingHom.comp_apply, map_teichmuller, fontaineTheta_teichmuller, untilt_tiltHom])
  exact RingHom.congr_fun key a

theorem coeff_eq_mk_zeta (ε : PreTilt O p) (n : ℕ) :
    PreTilt.coeff n ε = Ideal.Quotient.mk (Ideal.span {(p : O)}) (zeta ε n) := by
  rw [zeta, PreTilt.mk_untilt_eq_coeff_zero]
  change _ = PreTilt.coeff 0 ((_root_.frobeniusEquiv (PreTilt O p) p).symm^[n] ε)
  rw [PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add]

end Tilt

theorem exists_over {p : ℕ} [Fact p.Prime] (S S' : CycPerfd p) [Algebra S.R S'.R]
    (hz : ∀ n, zeta S'.ε n = algebraMap S.R S'.R (zeta S.ε n)) : ∃ α, S.Over S' α := by
  refine ⟨WittVector.map (tiltHom p (algebraMap S.R S'.R)), fontaineTheta_tiltHom p _, fun a => ?_, ?_⟩
  · ext n
    simp [coeff_frobenius_charP]
  · rw [map_teichmuller]
    congr 1
    refine Perfection.ext (R := ModP S'.R p) (p := p) fun n => ?_
    exact (coeff_tiltHom p _ _ n _ (coeff_eq_mk_zeta p _ n)).trans (by rw [← hz]; exact (coeff_eq_mk_zeta p _ n).symm)

section Tr

variable {A B A' B' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] {a b h : ℕ} (e : a = h) (e' : b = h)
  (M : Matrix (Fin h) (Fin h) ℤ)

def tr (σ : A →+* B) : (Fin a → A) →ₛₗ[σ] (Fin b → B) where
  toFun x j := mv σ M (fun i => x (Fin.cast e.symm i)) (Fin.cast e' j)
  map_add' x y := funext fun j => by simp [mv, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  map_smul' c x := funext fun j => by simp [mv, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]

theorem tr_apply (σ : A →+* B) (x : Fin a → A) (j : Fin b) :
    tr e e' M σ x j = ∑ i, (M (Fin.cast e' j) i : B) * σ (x (Fin.cast e.symm i)) := rfl

theorem piMap_tr {σ : A →+* B} {σ' : A' →+* B'} {u : A →+* A'} {v : B →+* B'} (k : ∀ x, v (σ x) = σ' (u x))
    (x : Fin a → A) : piMap v _ (tr e e' M σ x) = tr e e' M σ' (piMap u _ x) :=
  funext fun j => by simp [tr_apply, k]

end Tr

section Lat

variable {p : ℕ} [Fact p.Prime] (D : PrismData p) {S S' : CycPerfd p} {h : ℕ}

theorem coord_covMap {G G' : PDivGroup p S.R} (c : ConstTate (eps S) G) (c' : ConstTate (eps S) G') (e : G.height = h)
    (e' : G'.height = h) (f : G ⟶ G') (M : Matrix (Fin h) (Fin h) ℤ)
    (hf : ∀ j : Fin h, tateMap _ _ S.R (dualHom _ G' f) (c'.t' (Fin.cast e'.symm j)) =
      ∑ i : Fin h, M j i • c.t' (Fin.cast e.symm i)) (m : D.Cov G) :
    coord D c' (D.covMap G G' f m) = tr e e' M (RingHom.id _) (coord D c m) := by
  funext j
  have h1 := hf (Fin.cast e' j)
  change D.eCoord S (D.map S _ _ (constHom _ (c'.t' j)) (D.map S _ _ (dualHom G G' f) m)) = _
  rw [← LinearMap.comp_apply, ← D.map_comp, LatticeBaseChange.constHom_comp]
  change tateMap _ _ S.R (dualHom _ G' f) (c'.t' j) = _ at h1
  rw [h1, tr_apply]
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, coord_apply, RingHom.id_apply, zsmul_eq_mul]

variable [Algebra S.R S'.R] {α : Ainf p S.R →+* Ainf p S'.R} {G : PDivGroup p S.R} {G' : PDivGroup p S'.R}
  {c : ConstTate (eps S) G} {c' : ConstTate (eps S') G'} {e : G.height = h} {e' : G'.height = h}
  {M : Matrix (Fin h) (Fin h) ℤ}

theorem map_zeta_sub_one (hα : S.Over S' α) (n : ℕ) : algebraMap S.R S'.R (zeta S.ε n - 1) = zeta S'.ε n - 1 := by
  have h1 := muRoot_eps_of_over hα n
  rw [muRoot_eps, muRoot_eps] at h1
  rw [map_sub, map_one, h1]

theorem tr_theta (hα : S.Over S' α) {n n' : ℕ} {k : Fin G.height → Ainf p S.R} {x : Fin G.height → S.R}
    (hk : (zeta S.ε n - 1) • piMap (fontaineTheta S.R p) _ k = (zeta S.ε n' - 1) • x) :
    (zeta S'.ε n - 1) • piMap (fontaineTheta S'.R p) _ (tr e e' M α k) =
      (zeta S'.ε n' - 1) • tr e e' M (algebraMap S.R S'.R) x := by
  rw [piMap_tr e e' M hα.1, ← map_zeta_sub_one hα, ← map_zeta_sub_one hα, ← (tr e e' M _).map_smulₛₗ,
    ← (tr e e' M _).map_smulₛₗ, hk]

theorem tr_mem_base (hα : S.Over S' α) {x : Fin G.height → S.R} (hx : x ∈ base S G.height) :
    tr e e' M (algebraMap S.R S'.R) x ∈ base S' G'.height := by
  obtain ⟨y, rfl⟩ := (mem_base S x).1 hx
  exact (mem_base S' _).2 ⟨_, by rw [map_smulₛₗ, map_zeta_sub_one hα]⟩

variable {D}

theorem tr_mem_K (hα : S.Over S' α) (hT : ∀ m, ∃ m', coord D c' m' = tr e e' M α (coord D c m)) (n : ℕ)
    {x : Fin G.height → Ainf p S.R} (hx : x ∈ K D c n) : tr e e' M α x ∈ K D c' n := by
  induction n generalizing x with
  | zero => obtain ⟨m, rfl⟩ := hx; exact hT m
  | succ n ih => rw [mem_K_succ, piMap_tr e e' M fun a => (hα.2.1 a).symm]; exact ih hx

theorem tr_mem_H (hα : S.Over S' α) (hT : ∀ m, ∃ m', coord D c' m' = tr e e' M α (coord D c m)) (n : ℕ)
    {x : Fin G.height → S.R} (hx : x ∈ H D c n) : tr e e' M (algebraMap S.R S'.R) x ∈ H D c' n := by
  obtain ⟨k, hk, h1⟩ := (mem_H D c n x).1 hx
  exact (mem_H D c' n _).2 ⟨_, tr_mem_K hα hT _ hk, tr_theta hα h1⟩

theorem b_eq_tr (hα : S.Over S' α) {m : D.Cov G} {m' : D.Cov G'} (hm : coord D c' m' = tr e e' M α (coord D c m)) :
    b D c' m' = tr e e' M (algebraMap S.R S'.R) (b D c m) :=
  (congrArg (piMap (fontaineTheta S'.R p) _) hm).trans (piMap_tr e e' M hα.1 _)

theorem tr_alDual (hα : S.Over S' α) (hT : ∀ m, ∃ m', coord D c' m' = tr e e' M α (coord D c m)) (y : G.Lie) :
    ∃ y', c'.alDual y' = tr e e' M (algebraMap S.R S'.R) (c.alDual y) := by
  obtain ⟨u, hu⟩ := b_eq_unit_smul_alDual p D S
  obtain ⟨u', hu'⟩ := b_eq_unit_smul_alDual p D S'
  obtain ⟨m, rfl⟩ := D.toLie_surjective G y
  obtain ⟨m', hm⟩ := hT m
  refine ⟨algebraMap S.R S'.R (u⁻¹ : S.Rˣ) • (u' : S'.R) • D.toLie G' m', ?_⟩
  rw [map_smul, map_smul, ← (hu' G' c').1, b_eq_tr hα hm, ← map_smulₛₗ, (hu G c).1, smul_smul, Units.inv_mul, one_smul]

end Lat

theorem exists_congr_of_mem_span {A A' R R' : Type} [CommRing A] [CommRing A'] [CommRing R] [CommRing R'] [Algebra A R]
    [Algebra A' R'] (φ : A →+* A') (σ : R →+* R') (hφ : ∀ a, σ (algebraMap A R a) = algebraMap A' R' (φ a)) {k h : ℕ}
    (e : k = h) (π : A) (hπ : ModIso R π) (hπ' : ModIso R' (φ π)) (H : Submodule R (Fin k → R))
    (hH : ∀ y, algebraMap A R π • y ∈ H) (L : Submodule A (Fin h → A))
    (hL : ∀ x : Fin h → A, (fun i => algebraMap A R (x (Fin.cast e i))) ∈ H → x ∈ L) {z : Fin k → R'}
    (hz : z ∈ Submodule.span R' (piMap σ (Fin k) '' (H : Set (Fin k → R)))) :
    ∃ a ∈ Submodule.span A' (piMap φ (Fin h) '' (L : Set (Fin h → A))),
      ∀ j, algebraMap A' R' (φ π) ∣ z (Fin.cast e.symm j) - algebraMap A' R' (a j) := by
  subst e
  simp only [Fin.cast_refl, id] at hL ⊢
  induction hz using Submodule.span_induction with
  | mem _ hy =>
    obtain ⟨y, hy, rfl⟩ := hy
    choose x w hw using fun j => hπ.1 (y j)
    refine ⟨_, Submodule.subset_span ⟨x, hL x ?_, rfl⟩, fun j => ⟨σ (w j), ?_⟩⟩
    · convert H.sub_mem hy (hH w) using 1
      funext j
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← hw, sub_sub_cancel]
    · rw [piMap_apply, piMap_apply, ← hφ, ← hφ, ← map_sub, hw, map_mul]
  | zero => exact ⟨0, Submodule.zero_mem _, fun j => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, h1⟩ := hx
    obtain ⟨b, hb, h2⟩ := hy
    refine ⟨a + b, Submodule.add_mem _ ha hb, fun j => ?_⟩
    convert (h1 j).add (h2 j) using 1
    simp only [Pi.add_apply, map_add]; ring
  | smul r x _ hx =>
    obtain ⟨a, ha, h1⟩ := hx
    obtain ⟨s, hs⟩ := hπ'.1 r
    refine ⟨s • a, Submodule.smul_mem _ _ ha, fun j => ?_⟩
    convert ((h1 j).mul_left r).add (hs.mul_right (algebraMap A' R' (a j))) using 1
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring

theorem mapSt : MapSt := by
  intro p _ D S S' _ G G' c c' A A' _ _ _ _ φ h o e e' π π' γ γ' Lie Om Lie' Om' _ _ _ _ _ _ _ _ iL iO iL' iO' C C' f M l m
    hC hC' hφ hz hf hl hm
  obtain ⟨α, hα⟩ := exists_over S S' hz
  obtain ⟨⟨bc, -, hbc⟩, hsp⟩ := LatticeBaseChange.baseChange_lattices p D S S' α hα G c
  have hcov := coord_covMap D (c.baseChange S'.R (muRoot_eps_of_over hα)) c' e e' f M hf
  have hT : ∀ m, ∃ m', coord D c' m' = tr e e' M α (coord D c m) := fun m =>
    ⟨_, (hcov (bc m)).trans (funext fun j => by simp only [tr_apply, hbc, RingHom.id_apply])⟩
  have hR : ∀ {x : Fin h → A} {x' : Fin h → A'}, x' = mv φ M x →
      toR e' x' = tr e e' M (algebraMap S.R S'.R) (toR e x) := by
    rintro x _ rfl
    funext j
    simp [toR, tr_apply, mv, Matrix.mulVec, dotProduct, hφ]
  have hl' : ∀ y, c'.alDual (iL' (l y)) = tr e e' M (algebraMap S.R S'.R) (c.alDual (iL y)) := fun y =>
    funext fun j => hl y (Fin.cast e' j)
  have hmem : ∀ n, ∀ x ∈ C.L n, mv φ M x ∈ C'.L n := fun n x hx =>
    (hC'.mem n _).2 (hR rfl ▸ tr_mem_H hα hT n ((hC.mem n x).1 hx))
  refine ⟨⟨hmem, fun y x x' hx k => ?_, fun w x x' hx k => ?_, fun n hn x x' y y' hx hy k => ?_,
    fun n hn x x' y hx k => ?_⟩, fun hi hM hπ h1 h2 n => ?_⟩
  · rw [hC'.j, hR hx, hl', ← map_sub]
    exact tr_mem_base hα ((hC.j y x).1 k)
  · obtain ⟨x₀, h0, h1, h2⟩ := (hC.ρ w x).1 k
    refine (hC'.ρ _ _).2 ⟨_, tr_mem_H hα hT 0 h0, hm w x₀ h1, ?_⟩
    obtain ⟨u, hu, _, ⟨v, rfl⟩, h3⟩ := Submodule.mem_sup.1 h2
    rw [hR hx, ← map_sub, ← h3, map_add]
    exact Submodule.add_mem_sup (tr_mem_base hα hu) (tr_alDual hα hT v)
  · obtain ⟨k₀, h0, h1, y₀, h2, h3⟩ := (hC.ψ n hn x y).1 k
    refine (hC'.ψ n hn _ _).2 ⟨_, tr_mem_K hα hT _ h0, hR hx ▸ tr_theta hα h1, tr e e' M (algebraMap S.R S'.R) y₀, ?_, ?_⟩
    · rw [piMap_tr e e' M fun a => (hα.2.1 a).symm]
      exact tr_theta hα h2
    · rw [hR hy, ← map_sub]
      exact tr_mem_base hα h3
  · obtain ⟨m₀, h0, y₀, h1, h2⟩ := (hC.κ n hn x y).1 k
    obtain ⟨m', hm'⟩ := hT m₀
    obtain ⟨z, -, hz'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h2
    obtain ⟨z', h3⟩ := tr_alDual hα hT z
    refine (hC'.κ n hn _ _).2 ⟨m', ?_, iL' (l y) - (p : S'.R) • z', ?_, ?_⟩
    · rw [hR hx, ← tr_theta (e := e) (e' := e') (M := M) hα h0, hm']
      congr 2
      funext j
      simp only [tr_apply, LatticeBaseChange.map_phiInv hα]
      simp only [← RingHom.coe_pow, map_sum, map_mul, map_intCast]
    · rw [map_sub, map_smul, hl', h3, ← map_natCast (algebraMap S.R S'.R), ← map_smulₛₗ, ← map_sub, ← map_smul,
        ← map_sub, hz', sub_sub_cancel, h1, b_eq_tr hα hm']
    · rw [sub_sub_cancel]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  · subst hM hπ
    have hmv : ∀ x, mv φ (1 : Matrix (Fin h) (Fin h) ℤ) x = piMap φ _ x := fun x => by
      rw [mv, Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.one_mulVec]; rfl
    refine le_antisymm (fun x' hx' => ?_) (Submodule.span_le.2 ?_)
    swap
    · rintro _ ⟨x, hx, rfl⟩
      exact hmv x ▸ hmem n x hx
    have hone : ∀ {B : Type} [CommRing B] {a b : ℕ} (u : a = h) (v : b = h) (x : Fin a → B) (j : Fin b),
        tr u v 1 (RingHom.id B) x j = x (Fin.cast u.symm (Fin.cast v j)) := fun u v x j => congrFun (mv_id _) _
    have hT' : ∀ m', ∃ m₀, coord D (c.baseChange S'.R (muRoot_eps_of_over hα)) m₀ =
        tr (b := (G.baseChange S'.R).height) e' e 1 (RingHom.id _) (coord D c' m') := fun m' => by
      refine ⟨D.covMap _ _ (inv f) m', funext fun j => ?_⟩
      have h3 : D.covMap _ _ f (D.covMap _ _ (inv f) m') = m' := by
        change D.map S' _ _ (dualHom _ _ f) (D.map S' _ _ (dualHom _ _ (inv f)) m') = m'
        rw [← LinearMap.comp_apply, ← D.map_comp, ← dualHom_comp, IsIso.inv_hom_id, dualHom_id, D.map_id,
          LinearMap.id_apply]
      conv_rhs => rw [← h3, hcov, hone, hone]
      rfl
    have h3 := tr_mem_H S'.over_refl hT' n ((hC'.mem n x').1 hx')
    rw [hsp] at h3
    obtain ⟨a, ha, h4⟩ := exists_congr_of_mem_span φ _ hφ e π h1 h2 (H D c n)
      (fun y => base_le_H D c n ((mem_base S _).2 ⟨y, by rw [hC.pi_eq]⟩)) (C.L n) (fun x hx => (hC.mem n x).2 hx) h3
    have h5 : ∀ j, φ π ∣ x' j - a j := fun j => h2.2 _ (by
      rw [map_sub]
      exact (congrArg (fun t => algebraMap A' S'.R (φ π) ∣ t - algebraMap A' S'.R (a j))
        (hone e' e (toR e' x') (Fin.cast e.symm j))).mp (h4 j))
    choose w hw using h5
    have h6 : x' = a + ∑ j, w j • piMap φ _ (π • Pi.single j (1 : A)) := funext fun j => by
      simp [Finset.sum_apply, Pi.single_apply, apply_ite φ, mul_comm (w j), ← hw]
    rw [h6]
    exact Submodule.add_mem _ ha (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨_, C.base_le n (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top), rfl⟩))

end GlobalTheory.RingChain.RingMap

end
