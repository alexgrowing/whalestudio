import Development.EtaleCohomology.TateTwists.TwLocPfR

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TwTorsPf

section Field
variable {q : ℕ} [NeZero q] {k : Type} [Field k]

theorem prim_isPrim (ζ : Prim q k) : IsPrimitiveRoot ζ.1 q := by
  haveI : NeZero (q : k) := ⟨ζ.2.1.ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have h := ζ.2.2
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic] using h

theorem pow_eq_pow_cast {ζ : k} (h : IsPrimitiveRoot ζ q) {m n : ℕ} (e : ζ ^ m = ζ ^ n) :
    (m : ZMod q) = (n : ZMod q) := by
  have h0 : ζ ≠ 0 := h.ne_zero (NeZero.ne q)
  have e' : ζ ^ ((m : ℤ) - n) = 1 := by
    rw [zpow_sub₀ h0, zpow_natCast, zpow_natCast, e, div_self (pow_ne_zero _ h0)]
  have hd := (h.zpow_eq_one_iff_dvd _).1 e'
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub (n : ℤ) (m : ℤ) q).2 hd
  exact_mod_cast this.symm
end Field

section Field2
variable {q : ℕ} [NeZero q] {k : Type} [Field k]

def ex (ζ0 ξ : Prim q k) : ℕ :=
  ((prim_isPrim ζ0).eq_pow_of_pow_eq_one (prim_isPrim ξ).pow_eq_one).choose

theorem ex_spec (ζ0 ξ : Prim q k) : ζ0.1 ^ ex ζ0 ξ = ξ.1 :=
  ((prim_isPrim ζ0).eq_pow_of_pow_eq_one (prim_isPrim ξ).pow_eq_one).choose_spec.2

theorem ex_cop (ζ0 ξ : Prim q k) : (ex ζ0 ξ).Coprime q := by
  have h := prim_isPrim ξ
  rw [← ex_spec ζ0 ξ] at h
  exact ((prim_isPrim ζ0).pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) _).1 h

theorem ex_eq (ζ0 ξ : Prim q k) {m : ℕ} (h : ζ0.1 ^ m = ξ.1) : (ex ζ0 ξ : ZMod q) = m :=
  pow_eq_pow_cast (prim_isPrim ζ0) ((ex_spec ζ0 ξ).trans h.symm)

def exU (ζ0 ξ : Prim q k) : (ZMod q)ˣ := ZMod.unitOfCoprime _ (ex_cop ζ0 ξ)

theorem exU_rel (ζ0 η ξ : Prim q k) (a : (ZMod q)ˣ) (h : ξ.1 = η.1 ^ (a : ZMod q).val) :
    exU ζ0 ξ = exU ζ0 η * a := by
  ext
  simp only [exU, ZMod.coe_unitOfCoprime, Units.val_mul]
  rw [ex_eq ζ0 ξ (m := ex ζ0 η * (a : ZMod q).val)]
  · push_cast
    rw [ZMod.natCast_zmod_val]
  · rw [pow_mul, ex_spec, h]

theorem exU_self (ζ0 : Prim q k) : exU ζ0 ζ0 = 1 := by
  ext
  simp only [exU, ZMod.coe_unitOfCoprime, Units.val_one]
  rw [ex_eq ζ0 ζ0 (m := 1) (pow_one _)]
  simp

def val (i : ℤ) (ζ0 ξ : Prim q k) : ULift.{1} (ZMod q) := ULift.up (((exU ζ0 ξ) ^ i : (ZMod q)ˣ) : ZMod q)

def fn (i : ℤ) (ζ0 : Prim q k) : (Prim q k →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination _ (val i ζ0)

theorem rel_le (i : ℤ) (ζ0 : Prim q k) : twRel q i k ≤ LinearMap.ker (fn i ζ0) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨η, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, fn, Finsupp.linearCombination_single]
  rw [sub_eq_zero, val, val, exU_rel ζ0 η ξ a h, mul_zpow]
  apply ULift.ext
  simp [mul_comm]

theorem field_tors (i : ℤ) (ζ : Prim q k) (c : ℕ)
    (h : c • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q k →₀ ULift.{1} (ZMod q)) ⧸ twRel q i k) = 0) :
    q ∣ c := by
  have h2 := congrArg ((twRel q i k).liftQ (fn i ζ) (rel_le i ζ)) h
  rw [map_nsmul, map_zero, Submodule.liftQ_apply, fn, Finsupp.linearCombination_single, val, exU_self] at h2
  have h3 := congrArg ULift.down h2
  simp at h3
  exact (ZMod.natCast_eq_zero_iff c q).1 (by simpa using h3)
end Field2

theorem twF_map_mk {q : ℕ} (i : ℤ) {A B : CommRingCat.{0}} (φ : A ⟶ B) (ζ : Prim q A) :
    ((twF q i).map φ).hom (Submodule.Quotient.mk (Finsupp.single ζ 1)) =
      Submodule.Quotient.mk (Finsupp.single (ζ.map φ.hom) 1) := by
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map φ.hom) (Finsupp.single ζ 1)) = _
  rw [Finsupp.mapDomain_single]

theorem ring_tors {q : ℕ} [NeZero q] (i : ℤ) {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) (c : ℕ)
    (h : c • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) = 0) :
    q ∣ c := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  let f : A →+* A ⧸ m := Ideal.Quotient.mk m
  have h2 := congrArg (Submodule.mapQ _ _ (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q)) (Prim.map f))
    (twRel_le q i f)) h
  rw [map_nsmul, map_zero, Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] at h2
  exact field_tors i (ζ.map f) c h2

theorem jsEt : Scheme.JointlySurjective (Scheme.precoverage @AlgebraicGeometry.Etale.{0}) where
  exists_eq {X} R := fun ⟨hR, _⟩ x ↦ by
    rw [Scheme.jointlySurjectivePrecoverage, Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hR
    obtain ⟨Y, g, hg, heq⟩ := hR x
    exact ⟨Y, g, hg, heq⟩

theorem TwTors_of : LateralTheory.EtaleFoundations.TwLocPf.TwTors := by
  intro q _ i U _ ζ c hc
  let P := Scheme.Γ ⋙ twF q i
  let x : P.obj (op U) := Submodule.Quotient.mk (Finsupp.single ζ 1)
  have h1 : (toSheafify Scheme.etaleTopology P).app (op U) (c • x) =
      (toSheafify Scheme.etaleTopology P).app (op U) 0 := by
    have : ((toSheafify Scheme.etaleTopology P).app (op U)).hom (c • x) = 0 := by
      rw [map_nsmul]; exact hc
    simpa using this
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) (c • x) 0 h1
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  haveI := jsEt
  obtain ⟨j, y, -⟩ := 𝒰.exists_eq (Classical.arbitrary U)
  have hj := hle _ _ (Presieve.ofArrows.mk j)
  simp only [Presheaf.equalizerSieve_apply, map_zero] at hj
  have : Nonempty (𝒰.X j) := ⟨y⟩
  have : Nonempty (⊤ : (𝒰.X j).Opens) := ⟨⟨y, trivial⟩⟩
  have h3 : ((twF q i).map (𝒰.f j).appTop).hom (c • x) = 0 := hj
  have h4 : c • ((twF q i).map (𝒰.f j).appTop).hom (Submodule.Quotient.mk (Finsupp.single ζ 1)) = 0 :=
    (map_nsmul ((twF q i).map (𝒰.f j).appTop).hom c _).symm.trans h3
  rw [twF_map_mk] at h4
  exact ring_tors i _ c h4

end LateralTheory.EtaleFoundations.TwTorsPf
