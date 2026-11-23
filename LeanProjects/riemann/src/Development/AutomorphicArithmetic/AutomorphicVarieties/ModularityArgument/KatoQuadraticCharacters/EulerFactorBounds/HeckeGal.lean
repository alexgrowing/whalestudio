import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.GalAct
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb.HG

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem ent_toGQ (m : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) (i j : Fin 2) : ent (toGQ m) i j = (m i j : ℚ) := by
  simp [ent, toGQ, h]

private theorem gal_diag (X : Tower Ω ε) (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (s : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.gal s (X.sl (toGQ !![a, 0; 0, b]) f) = X.sl (toGQ !![a, 0; 0, b]) (X.gal s f) := by
  have hd : 0 < (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    rw [Matrix.det_fin_two_of]; simpa using mul_pos ha hb
  have h1 : eOm ε 0 = 1 := by
    have := Function.leftInverse_invFun ε.injective 1
    simpa [eOm] using this
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have key : ∀ (f : X.K) (r : ℚ), (X.exp (X.sl (toGQ !![a, 0; 0, b]) f)).coeff r = (X.exp f).coeff (r * b / a) := by
    intro f r
    have := X.exp_upper (toGQ !![a, 0; 0, b]) (by rw [ent_toGQ _ hd]; simp) f (r * b / a)
    rw [ent_toGQ _ hd, ent_toGQ _ hd, ent_toGQ _ hd] at this
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Int.cast_zero, mul_zero, zero_div, h1, one_mul] at this
    rw [← this]; congr 1; field_simp
  apply X.exp.toRingHom.injective
  ext r
  show (X.exp _).coeff r = (X.exp _).coeff r
  rw [X.gal_exp, key, key, X.gal_exp]

private theorem galB_diag (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (p : ℤ) (hp : 0 < p) (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) :
    X.galB l s (X.act l !![p, 0; 0, 1] b) = X.act l !![p, 0; 0, 1] (X.galB l s b) := by
  funext u
  show X.kmap l _ (X.kmap l _ (b _)) = X.kmap l _ (X.kmap l _ (b _))
  rw [X.kmap_kmap, X.kmap_kmap]
  congr 2
  · ext f; exact gal_diag X p 1 hp one_pos s f
  · funext i
    fin_cases i <;> simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private def tr (t : ℤ) : SL(2, ℤ) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

private theorem sl_up (X : Tower Ω ε) (p : ℤ) (hp : 0 < p) (j : ℤ) (f : X.K) :
    X.sl (toGQ !![1, j; 0, p]) f = X.sl (ofSL (tr j)) (X.sl (toGQ !![1, 0; 0, p]) f) := by
  rw [← X.sl_mul, ← Betti.toGQ_sl, ← toGQ_mul_of_pos _ _ (by simpa [Matrix.det_fin_two_of] using hp)
    (by rw [(tr j).det_coe]; exact one_pos)]
  congr 3
  simp [tr]

private theorem recip_up (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (p : ℤ) (hp : 0 < p) (s : Ω ≃ₐ[ℚ] Ω) (x : X.Khat l) :
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ (M : ℕ) (ζ : Ω) (e : ℕ), 0 < M → M₀ ∣ M → IsPrimitiveRoot ζ M → s ζ = ζ ^ e → ∀ j : ℤ,
      AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l (X.gal s) (X.kmap l (X.sl (toGQ !![1, j; 0, p])).toRingEquiv x)) =
      AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l (X.sl (toGQ !![1, j * e; 0, p])).toRingEquiv (X.kmap l (X.gal s) x)) := by
  have hc := GlobalTheory.KZ.H3.cls_props Ω ε X l n
  obtain ⟨f, hf⟩ := hc.1 (AdicCompletion.eval (idl l) (X.Kl l) n x)
  obtain ⟨M₀, h0, hl⟩ := X.level (X.sl (toGQ !![1, 0; 0, p]) (f : X.K))
  refine ⟨M₀, h0, fun M ζ e hM hd hζ hs j => ?_⟩
  have hF := hc.2.2.2.2.2.1
  rw [hF _ _ _ (hF _ _ _ hf.symm), hF _ _ _ (hF _ _ _ hf.symm)]
  congr 1
  apply Units.ext
  show X.gal s (X.sl _ (f : X.K)) = X.sl _ (X.gal s (f : X.K))
  rw [sl_up X p hp j, sl_up X p hp (j * e), ← gal_diag X 1 p one_pos hp]
  obtain ⟨k, hk⟩ := hd
  have hk0 : 0 < k := Nat.pos_of_mul_pos_left (hk ▸ hM)
  have hζ' : IsPrimitiveRoot (ζ ^ k) M₀ := hζ.pow hM (by rw [hk, mul_comm])
  refine X.recip M₀ _ h0 hl (ζ ^ k) hζ' s e ?_ _ _ ?_
  · rw [map_pow, hs, zpow_natCast, ← pow_mul, ← pow_mul, mul_comm]
  · simp [en, tr, mul_comm]

private theorem expo [IsAlgClosure ℚ Ω] (l n M : ℕ) [Fact l.Prime] (hM : 0 < M) (hd : l ^ n ∣ M) (s : Ω ≃ₐ[ℚ] Ω) :
    ∃ (ζ : Ω) (e : ℕ), IsPrimitiveRoot ζ M ∧ s ζ = ζ ^ e ∧ Nat.Coprime e M ∧
      (l : ℤ_[l]) ^ n ∣ (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) - e := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hs : IsPrimitiveRoot (s ζ) M := hζ.map_of_injective s.injective
  obtain ⟨e, -, he⟩ := hζ.eq_pow_of_pow_eq_one hs.pow_eq_one
  refine ⟨ζ, e, hζ, he.symm, (hζ.pow_iff_coprime hM e).1 (he ▸ hs), ?_⟩
  obtain ⟨k, hk⟩ := hd
  have ht : IsPrimitiveRoot (ζ ^ k) (l ^ n) := hζ.pow hM (by rw [hk, mul_comm])
  have h1 := cyclotomicCharacter.spec l (n := n) s.toRingEquiv (ζ ^ k) ht.pow_eq_one
  have h2 : s.toRingEquiv (ζ ^ k) = (ζ ^ k) ^ e := by
    show s (ζ ^ k) = _
    rw [map_pow, ← he, ← pow_mul, ← pow_mul, mul_comm]
  rw [h2] at h1
  have h3 := (ht.isOfFinOrder (pow_pos (Fact.out : l.Prime).pos n).ne').pow_eq_pow_iff_modEq.1 h1
  rw [← ht.eq_orderOf] at h3
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
    (ZMod.natCast_eq_natCast_iff _ _ _).2 h3, ZMod.natCast_zmod_val, sub_self]

private theorem sum_perm {Q : Type} [AddCommMonoid Q] (p e : ℕ) (hp : 0 < p) (he : Nat.Coprime e p) (F : ℤ → Q)
    (hF : ∀ k t : ℤ, F (k + t * p) = F k) : ∑ j ∈ Finset.range p, F (j * e) = ∑ j ∈ Finset.range p, F j := by
  haveI : NeZero p := ⟨hp.ne'⟩
  have h1 : ∀ k : ℤ, F k = F ((k : ZMod p).val) := by
    intro k
    rw [ZMod.val_intCast, ← hF (k % p) (k / p)]
    congr 1
    rw [mul_comm]; exact (Int.emod_add_mul_ediv k p).symm
  have h2 : ∀ G : ZMod p → Q, ∑ j ∈ Finset.range p, G j = ∑ x, G x := fun G =>
    Finset.sum_nbij' (fun j => (j : ZMod p)) ZMod.val (by simp) (by simp [ZMod.val_lt])
      (fun j hj => ZMod.val_cast_of_lt (by simpa using hj)) (by simp) (by simp)
  have h3 := h2 fun x => F (x * e).val
  have h4 := h2 fun x => F x.val
  rw [Finset.sum_congr rfl fun (j : ℕ) _ => h1 (j * e), Finset.sum_congr rfl fun (j : ℕ) _ => h1 j]
  push_cast
  rw [h3, h4]
  exact Equiv.sum_comp (ZMod.unitOfCoprime e he).mulRight fun x => F x.val

private theorem eval_kmap (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (φ : X.K ≃+* X.K) {x y : X.Khat l}
    (h : AdicCompletion.eval (idl l) (X.Kl l) n x = AdicCompletion.eval (idl l) (X.Kl l) n y) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ x) = AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ y) := by
  have hc := GlobalTheory.KZ.H3.cls_props Ω ε X l n
  obtain ⟨f, hf⟩ := hc.1 (AdicCompletion.eval (idl l) (X.Kl l) n y)
  rw [hc.2.2.2.2.2.1 φ x f (h.trans hf.symm), hc.2.2.2.2.2.1 φ y f hf.symm]

private theorem poly_cg (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (a t : X.Fn l)
    (ht : PolMod X l w n t) (h : CgF X l n a t) (u v : Fin 2 → ℤ_[l]) (h0 : (l : ℤ_[l]) ^ n ∣ u 0 - v 0) (h1 : u 1 = v 1) :
    AdicCompletion.eval (idl l) (X.Kl l) n (a u) = AdicCompletion.eval (idl l) (X.Kl l) n (a v) := by
  obtain ⟨c, -, hc⟩ := ht
  have hu := h u
  have hv := h v
  rw [map_sub, sub_eq_zero] at hu hv
  rw [hu, hv, hc, hc, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (c i))
  rw [map_smul, map_smul, ← hx, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
    ← sub_smul]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, h1, ← sub_mul]
  exact (h0.trans (sub_dvd_pow_sub_pow _ _ _)).mul_right _

private theorem cg_act (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) {a b : X.Fn l}
    (h : CgF X l n a b) : CgF X l n (X.act l m a) (X.act l m b) := by
  intro u
  have := h (mZl l m *ᵥ u)
  rw [map_sub, sub_eq_zero] at this ⊢
  exact eval_kmap X l n _ this

private theorem cg_add (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) {a b a' b' : X.Fn l}
    (h : CgF X l n a b) (h' : CgF X l n a' b') : CgF X l n (a + a') (b + b') := by
  intro u
  rw [Pi.add_apply, Pi.add_apply, add_sub_add_comm, map_add, h u, h' u, add_zero]

end UpperTheory.V.Z.Kato.Nb.HG

open UpperTheory.V.Z.Kato.Nb.HG in
theorem UpperTheory.V.Z.Kato.Nb.sHeckeGal :
    UpperTheory.V.Z.Kato.Nb.SHeckeGal := by
  intro Ω _ _ _ ε X l hl N w n p hN hp hc s a ha
  obtain ⟨ha', hG⟩ := sGalAct Ω ε X l N w n hN s a ha
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hσ := (Betti.isDiam_sgD hN.ne' hl.out.ne_zero (Nat.Coprime.coprime_mul_left_right hc)).1
  have hD : 0 < (!![(p : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by simpa [Matrix.det_fin_two_of] using hp.pos
  have hS : ∀ γ : SL(2, ℤ), 0 < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := fun γ => by rw [γ.det_coe]; exact one_pos
  unfold Tower.heckeT
  rw [LinearMap.add_apply, LinearMap.add_apply, map_add]
  refine cg_add X l n ?_ ?_
  · intro u
    set χ : ℤ_[l] := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hχ
    choose M₀ hM₀ hR using fun j : ℕ => recip_up X l n p hp' s (a (mZl l !![1, (j : ℤ); 0, (p : ℤ)] *ᵥ ![u 0, χ * u 1]))
    have hM : 0 < (∏ j ∈ Finset.range p, M₀ j) * (l ^ n * p) :=
      Nat.mul_pos (Finset.prod_pos fun j _ => hM₀ j) (Nat.mul_pos (pow_pos hl.out.pos n) hp.pos)
    obtain ⟨ζ, e, hζ, hs, he, hχe⟩ := expo l n _ hM ((Dvd.intro _ rfl : l ^ n ∣ _).mul_left _) s
    obtain ⟨t, ht, hat⟩ := ha.1
    have hper : ∀ k t : ℤ,
        AdicCompletion.eval (idl l) (X.Kl l) n (X.act l !![1, k + t * p; 0, (p : ℤ)] (X.galB l s a) u) =
        AdicCompletion.eval (idl l) (X.Kl l) n (X.act l !![1, k; 0, (p : ℤ)] (X.galB l s a) u) := by
      intro k t
      have hg : tr t ∈ Gam N l := ⟨(CongruenceSubgroup.Gamma1_mem N _).2 (by simp [tr]),
        CongruenceSubgroup.Gamma0_mem.2 (by simp [tr])⟩
      have := cg_act X l n !![1, k; 0, (p : ℤ)] (ha'.2.1 _ hg) u
      rw [Tower.act_act Ω ε X l _ _ (hS _) (by simpa [Matrix.det_fin_two_of] using hp.pos), map_sub, sub_eq_zero] at this
      rw [← this]
      congr 3
      simp [tr]
    have hsum := sum_perm p e hp.pos (he.coprime_dvd_right ((Dvd.intro_left _ rfl : p ∣ _).mul_left _))
      (fun k => AdicCompletion.eval (idl l) (X.Kl l) n (X.act l !![1, k; 0, (p : ℤ)] (X.galB l s a) u)) hper
    rw [map_sub, sub_eq_zero, LinearMap.sum_apply, LinearMap.sum_apply, map_sum, Finset.sum_apply, Finset.sum_apply,
      map_sum, map_sum, ← hsum]
    refine Finset.sum_congr rfl fun j hj => ?_
    refine (hR j _ ζ e hM ((Finset.dvd_prod_of_mem _ hj).mul_right _) hζ hs j).trans ?_
    refine eval_kmap X l n _ (eval_kmap X l n _ (poly_cg X l w n a t ht hat _ _ ?_ ?_))
    · have : (l : ℤ_[l]) ^ n ∣ j * u 1 * (χ - e) := hχe.mul_left _
      convert this using 1
      simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    · simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hχ]
      ring
  · rw [← Tower.act_act Ω ε X l _ _ (hS _) hD, ← Tower.act_act Ω ε X l _ _ (hS _) hD, galB_diag X l p hp']
    exact cg_act X l n _ (hG _ hσ).2
