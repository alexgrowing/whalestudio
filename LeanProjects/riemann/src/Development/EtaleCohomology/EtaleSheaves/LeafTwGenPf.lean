import Development.EtaleCohomology.EtaleSheaves.LeafTwSecKillCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8.TwSec.Gen

theorem prim_pow_eq_one {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hp
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

theorem prim_isPrimitiveRoot {q : ℕ} [NeZero q] {A K : Type} [CommRing A] [Field K] (φ : A →+* K) (ζ : Prim q A) :
    IsPrimitiveRoot (φ ζ.1) q := by
  have hu : IsUnit (q : K) := by simpa using ζ.2.1.map φ
  have : NeZero (q : K) := ⟨hu.ne_zero⟩
  have h := Polynomial.aeval_algHom_apply φ.toIntAlgHom ζ.1 (Polynomial.cyclotomic q ℤ)
  rw [ζ.2.2, map_zero] at h
  have h2 : Polynomial.aeval (φ ζ.1) (Polynomial.cyclotomic q ℤ) = 0 := by simpa using h
  rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic, ← Polynomial.IsRoot.def,
    Polynomial.isRoot_cyclotomic_iff] at h2

theorem exists_pow {q : ℕ} [NeZero q] {A K : Type} [CommRing A] [Field K] (φ : A →+* K) (ζ ξ : Prim q A) :
    ∃ k < q, k.Coprime q ∧ φ ξ.1 = φ ζ.1 ^ k := by
  have hζ := prim_isPrimitiveRoot φ ζ
  have hξ := prim_isPrimitiveRoot φ ξ
  obtain ⟨i, hi, e⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  refine ⟨i, hi, ?_, e.symm⟩
  exact (hζ.pow_iff_coprime (NeZero.pos q) i).mp (by rw [e]; exact hξ)

theorem key_ring {A K : Type} [CommRing A] [Field K] (φ : A →+* K) (x y : A) (q k : ℕ) (hq : (q : K) ≠ 0)
    (hx : x ^ q = 1) (hy : y ^ q = 1) (h : φ x = φ y ^ k) :
    φ (∑ b ∈ Finset.range q, (x * y ^ (k * (q - 1))) ^ b) ≠ 0 ∧
    ∀ (B : Type) [CommRing B] (ψ : A →+* B), IsUnit (ψ (∑ b ∈ Finset.range q, (x * y ^ (k * (q - 1))) ^ b)) →
      ψ x = ψ y ^ k := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hkq : k * (q - 1) + k = k * q := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.one_le_iff_ne_zero.mpr hq0); simp [mul_add]; ring
  have hyk : y ^ (k * (q - 1)) * y ^ k = 1 := by rw [← pow_add, hkq, mul_comm, pow_mul, hy, one_pow]
  have hu : (x * y ^ (k * (q - 1))) ^ q = 1 := by
    rw [mul_pow, hx, one_mul, ← pow_mul, mul_comm, pow_mul, hy, one_pow]
  refine ⟨?_, ?_⟩
  · have : φ (x * y ^ (k * (q - 1))) = 1 := by
      rw [map_mul, map_pow, h, ← pow_add, add_comm, hkq, mul_comm, pow_mul, ← map_pow, hy, map_one, one_pow]
    simpa [map_sum, map_pow, this] using hq
  · intro B _ ψ hs
    have h0 : ψ (∑ b ∈ Finset.range q, (x * y ^ (k * (q - 1))) ^ b) * (ψ (x * y ^ (k * (q - 1))) - 1) = 0 := by
      rw [← map_one ψ, ← map_sub, ← map_mul, geom_sum_mul, hu, sub_self, map_zero]
    have h1 : ψ (x * y ^ (k * (q - 1))) = 1 := by
      have := (hs.mul_right_eq_zero).mp h0
      exact sub_eq_zero.mp this
    calc ψ x = ψ x * ψ (y ^ (k * (q - 1)) * y ^ k) := by rw [hyk, map_one, mul_one]
      _ = ψ (x * y ^ (k * (q - 1))) * ψ y ^ k := by simp only [map_mul, map_pow]; ring
      _ = ψ y ^ k := by rw [h1, one_mul]

theorem isUnit_res {W : Scheme.{0}} (s : Γ(W, ⊤)) :
    IsUnit ((Scheme.Γ.map (W.basicOpen s).ι.op).hom s) := by
  set O := W.basicOpen s
  rw [Scheme.Γ_map_op]
  refine RingedSpace.isUnit_of_isUnit_germ O.toScheme.toRingedSpace ⊤ _ (fun y _ => ?_)
  have hy : y ∈ O.toScheme.basicOpen (O.ι.appTop s) := by
    rw [← Scheme.preimage_basicOpen_top]
    show O.ι y ∈ O
    exact y.2
  exact (Scheme.mem_basicOpen_top _ _ _).mp hy

end LateralTheory.E.E8.TwSec.Gen

namespace LateralTheory.E.E8.TwSec.Gen

theorem map_mk {q : ℕ} (j : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (ξ : Prim q A) (r : ULift.{1} (ZMod q)) :
    ((twF q j).map f).hom (Submodule.Quotient.mk (p := twRel q j A) (Finsupp.single ξ r)) =
      Submodule.Quotient.mk (p := twRel q j B) (Finsupp.single (ξ.map f.hom) r) := by
  change Submodule.Quotient.mk (Finsupp.mapDomain _ (Finsupp.single ξ r)) = _
  rw [Finsupp.mapDomain_single]

theorem mk_pow {q : ℕ} (j : ℤ) {B : CommRingCat.{0}} (ζ ξ : Prim q B) (k : ℕ) (hk : k < q) (hc : k.Coprime q)
    (h : ξ.1 = ζ.1 ^ k) :
    (Submodule.Quotient.mk (p := twRel q j B) (Finsupp.single ξ 1) : (twF q j).obj B) =
      ULift.up ((((ZMod.unitOfCoprime k hc) ^ j : (ZMod q)ˣ)) : ZMod q) • twCls j ζ := by
  unfold twCls
  have h1 : (ULift.up ((((ZMod.unitOfCoprime k hc) ^ j : (ZMod q)ˣ)) : ZMod q) : ULift.{1} (ZMod q)) •
      (Submodule.Quotient.mk (p := twRel q j B) (Finsupp.single ζ 1)) =
      Submodule.Quotient.mk (Finsupp.single ζ (ULift.up ((((ZMod.unitOfCoprime k hc) ^ j : (ZMod q)ˣ)) : ZMod q))) := by
    rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  refine Eq.trans ?_ h1.symm
  rw [Submodule.Quotient.eq]
  refine Submodule.subset_span ⟨ζ, ξ, ZMod.unitOfCoprime k hc, ?_, rfl⟩
  rw [h, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hk]

theorem res_le {q : ℕ} (j : ℤ) {W : Scheme.{0}} {O O' : W.Opens} (h : O' ≤ O) {x y : (twF q j).obj Γ(W, ⊤)}
    (e : ((twF q j).map (Scheme.Γ.map O.ι.op)).hom x = ((twF q j).map (Scheme.Γ.map O.ι.op)).hom y) :
    ((twF q j).map (Scheme.Γ.map O'.ι.op)).hom x = ((twF q j).map (Scheme.Γ.map O'.ι.op)).hom y := by
  rw [← W.homOfLE_ι h, op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp]
  exact congrArg (ModuleCat.Hom.hom ((twF q j).map (Scheme.Γ.map (W.homOfLE h).op))) e

theorem core {q : ℕ} [NeZero q] (j : ℤ) {W : Scheme.{0}} (ζ ξ : Prim q Γ(W, ⊤)) (w0 : W) :
    ∃ (O : W.Opens) (c : ZMod q), w0 ∈ O ∧
      ((twF q j).map (Scheme.Γ.map O.ι.op)).hom (Submodule.Quotient.mk (p := twRel q j Γ(W, ⊤)) (Finsupp.single ξ 1)) =
        ((twF q j).map (Scheme.Γ.map O.ι.op)).hom (ULift.up c • twCls j ζ) := by
  obtain ⟨k, hk, hc, e⟩ := exists_pow (W.Γevaluation w0).hom ζ ξ
  have hq : ((q : ℕ) : W.residueField w0) ≠ 0 := by
    have := ζ.2.1.map (W.Γevaluation w0).hom
    simpa using this.ne_zero
  obtain ⟨h1, h2⟩ := key_ring (W.Γevaluation w0).hom ξ.1 ζ.1 q k hq (prim_pow_eq_one ξ) (prim_pow_eq_one ζ) e
  refine ⟨W.basicOpen (∑ b ∈ Finset.range q, (ξ.1 * ζ.1 ^ (k * (q - 1))) ^ b),
    (((ZMod.unitOfCoprime k hc) ^ j : (ZMod q)ˣ) : ZMod q),
    (W.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) w0 trivial _).mp h1, ?_⟩
  have hs := h2 _ (Scheme.Γ.map (W.basicOpen (∑ b ∈ Finset.range q, (ξ.1 * ζ.1 ^ (k * (q - 1))) ^ b)).ι.op).hom
    (isUnit_res _)
  refine (map_mk j _ ξ 1).trans ?_
  refine Eq.trans ?_ (LinearMap.map_smul _ _ _).symm
  refine Eq.trans ?_ (congrArg _ (map_mk j _ ζ 1).symm)
  exact mk_pow j _ _ k hk hc hs

end LateralTheory.E.E8.TwSec.Gen

namespace LateralTheory.E.E8.TwSec

open Gen in
theorem LeafTwGen_of : LeafTwGen := by
  intro q _ j W ζ t w0
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (twRel q j Γ(W, ⊤)) t
  induction f using Finsupp.induction_linear with
  | zero =>
    refine ⟨⊤, 0, trivial, ?_⟩
    have hm : (Submodule.Quotient.mk 0 : (twF q j).obj Γ(W, ⊤)) = 0 := Submodule.Quotient.mk_zero _
    have h0 : (ULift.up (0 : ZMod q) : ULift.{1} (ZMod q)) • twCls j ζ = 0 := zero_smul _ _
    rw [hm, h0]
    exact rfl
  | add f g hf hg =>
    obtain ⟨O1, c1, h1, e1⟩ := hf
    obtain ⟨O2, c2, h2, e2⟩ := hg
    refine ⟨O1 ⊓ O2, c1 + c2, ⟨h1, h2⟩, ?_⟩
    have hm : (Submodule.Quotient.mk (f + g) : (twF q j).obj Γ(W, ⊤)) =
        (Submodule.Quotient.mk f : (twF q j).obj Γ(W, ⊤)) + (Submodule.Quotient.mk g : (twF q j).obj Γ(W, ⊤)) :=
      Submodule.Quotient.mk_add _
    rw [hm]
    refine (LinearMap.map_add _ _ _).trans ?_
    rw [res_le j inf_le_left e1, res_le j inf_le_right e2]
    refine (LinearMap.map_add _ _ _).symm.trans ?_
    congr 1
    exact (add_smul _ _ _).symm
  | single ξ r =>
    obtain ⟨O, c, h, e⟩ := core j ζ ξ w0
    refine ⟨O, r.down * c, h, ?_⟩
    have hr : Finsupp.single ξ r = r • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    have hm : (Submodule.Quotient.mk (r • Finsupp.single ξ (1 : ULift.{1} (ZMod q))) : (twF q j).obj Γ(W, ⊤)) =
        r • (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q j).obj Γ(W, ⊤)) :=
      Submodule.Quotient.mk_smul _ _ _
    rw [hr, hm]
    refine (LinearMap.map_smul _ _ _).trans ?_
    rw [e]
    refine (LinearMap.map_smul _ _ _).symm.trans ?_
    congr 1
    exact smul_smul _ _ _

end LateralTheory.E.E8.TwSec
