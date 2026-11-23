import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.SemiAbelianSchemes
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharpolyTateDetDegreeTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionGeometricPointsEqPowTwoDim
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharpolyLattice

theorem pts_equiv (k : Type) [Field k] [IsAlgClosed k] (B : GlobalTheory.AV.AbVar k) :
    ∃ e : (Over.mk (𝟙 (Sp k)) ⟶ B.X) ≃* B.Pt,
      ∀ (f : B ⟶ B) (q : Over.mk (𝟙 (Sp k)) ⟶ B.X), e (q ≫ f.hom) = e q ≫ f.hom := by
  have hb : Function.Bijective (algebraMap k (AlgebraicClosure k)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  haveI : IsIso (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) :=
    (RingEquiv.ofBijective _ hb).toCommRingCatIso.isIso_hom
  haveI : IsIso (spMap (algebraMap k (AlgebraicClosure k))) :=
    inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))
  let i : ptOver k (AlgebraicClosure k) ≅ Over.mk (𝟙 (Sp k)) :=
    Over.isoMk (asIso (spMap (algebraMap k (AlgebraicClosure k)))) (Category.comp_id _)
  refine ⟨{ toFun := fun q => i.hom ≫ q
            invFun := fun q => i.inv ≫ q
            left_inv := fun q => by simp
            right_inv := fun q => by simp
            map_mul' := fun q q' => MonObj.comp_mul _ _ _ }, fun f q => ?_⟩
  exact (Category.assoc i.hom q f.hom).symm

theorem charpoly_reduce {R S : Type} [CommRing R] [CommRing S] (π : R →+* S)
    (hπ : Function.Surjective π) (n : R) (hn : π n = 0)
    {N Q : Type} [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    [AddCommGroup Q] [Module S Q] (e : N →+ Q) (he : Function.Surjective e)
    (hsmul : ∀ (r : R) (x : N), e (r • x) = π r • e x) (hk : ∀ x, e x = 0 → ∃ y, x = n • y)
    (g : N →ₗ[R] N) (G : Q →ₗ[S] Q) (hg : ∀ x, e (g x) = G (e x)) :
    ∃ (_ : Module.Free S Q) (_ : Module.Finite S Q),
      LinearMap.charpoly G = (LinearMap.charpoly g).map π := by
  classical
  let b := Module.Free.chooseBasis R N
  have hsum : ∀ c : Module.Free.ChooseBasisIndex R N → R,
      e (∑ i, c i • b i) = ∑ i, π (c i) • e (b i) := fun c => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hsmul _ _
  have hli : LinearIndependent S fun i => e (b i) := by
    refine Fintype.linearIndependent_iff.2 fun s hs i => ?_
    choose c hc using fun i => hπ (s i)
    obtain ⟨y, hy⟩ := hk (∑ i, c i • b i) (by rw [hsum]; simpa only [hc] using hs)
    have h := congrArg (fun z => b.repr z i) hy
    simp only [Module.Basis.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
    rw [← hc, h, map_mul, hn, zero_mul]
  have hsp : ⊤ ≤ Submodule.span S (Set.range fun i => e (b i)) := by
    intro q _
    obtain ⟨x, rfl⟩ := he q
    rw [← b.sum_repr x, hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = e (b i) := fun i => Module.Basis.mk_apply hli hsp i
  refine ⟨Module.Free.of_basis b', Module.Finite.of_basis b', ?_⟩
  haveI := Module.Free.of_basis b'
  haveI := Module.Finite.of_basis b'
  rw [← LinearMap.charpoly_toMatrix G b', ← LinearMap.charpoly_toMatrix g b, ← Matrix.charpoly_map]
  congr 1
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hb', ← hg]
  conv_lhs => rw [← b.sum_repr (g (b j)), hsum]
  simp only [← hb']
  rw [Module.Basis.repr_sum_self]

open GlobalTheory.HTLat in

theorem lev_pow_smul {M : Type} [CommGroup M] {l : ℕ} [Fact l.Prime]
    (s : Tate l M) (j n : ℕ) : (((l : ℤ_[l]) ^ j) • s).lev n = s.lev n ^ l ^ j := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rfl

open GlobalTheory.HTLat in

theorem tate_lev_eq_one_iff (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime]
    (t : GlobalTheory.HTLat.Tate l M) (j : ℕ) :
    t.lev j = 1 ↔ ∃ s : GlobalTheory.HTLat.Tate l M, t = ((l : ℤ_[l]) ^ j) • s := by
  constructor
  · intro ht
    refine ⟨Tate.mk (fun n => t.lev (j + n)) fun n => ⟨by rw [Tate.lev_add_pow, ht], Tate.lev_succ t (j + n)⟩,
      Tate.ext fun n => ?_⟩
    rw [lev_pow_smul, Tate.lev_mk, add_comm, Tate.lev_add_pow]
  · rintro ⟨s, rfl⟩
    rw [lev_pow_smul, Tate.lev_pow]

open GlobalTheory.HTLat in

theorem tate_lev_surj (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (r : ℕ)
    (hc : ∀ n : ℕ, Nat.card {x : M // x ^ (l ^ n) = 1} = l ^ (r * n)) (j : ℕ) (x : M)
    (hx : x ^ (l ^ j) = 1) : ∃ t : GlobalTheory.HTLat.Tate l M, t.lev j = x := by
  choose L hL using GlobalTheory.TateFree.exists_pow_eq hc
  let u : ∀ m : ℕ, {y : M // y ^ l ^ (j + m) = 1} := fun m =>
    Nat.rec (motive := fun m => {y : M // y ^ l ^ (j + m) = 1}) ⟨x, hx⟩
      (fun m y => ⟨L (j + m) y.1 y.2, (hL _ _ _).1⟩) m
  have hu : ∀ m, (u (m + 1)).1 ^ l = (u m).1 := fun m => (hL _ _ _).2
  have hu' : ∀ m, (u m).1 ^ l ^ m = x := fun m => by
    induction m with
    | zero => exact pow_one x
    | succ m ih => rw [pow_succ', pow_mul, hu, ih]
  refine ⟨Tate.mk (fun m => (u m).1 ^ l ^ j) fun m => ⟨?_, ?_⟩, hu' j⟩
  · rw [← pow_mul, ← pow_add]
    exact (u m).2
  · rw [← pow_mul, mul_comm, pow_mul, hu]

end GlobalTheory.CharpolyLattice

namespace GlobalTheory.AV.AbVar

open GlobalTheory.CharpolyLattice GlobalTheory.HTLat in

theorem charpoly_eq_lattice_model : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B)
    (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (φ : L →ₗ[ℤ] L) (l : ℕ), l.Prime → (l : k) ≠ 0 →
    ∀ ev : ℕ → L → (Over.mk (𝟙 (Sp k)) ⟶ B.X),
    (∀ j x y, ev j (x + y) = ev j x * ev j y) →
    (∀ j x, ev j (φ x) = ev j x ≫ f.hom) →
    (∀ j x, ev j x = 1 ↔ ∃ y, x = l ^ j • y) →
    (∀ j (q : Over.mk (𝟙 (Sp k)) ⟶ B.X), q ^ (l ^ j) = 1 ↔ ∃ x, ev j x = q) →
    LinearMap.charpoly φ = GlobalTheory.AV.AbVar.charpoly f := by
  intro k _ _ B f L _ _ _ φ l hl hlk ev hadd hequi hker him
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨e, he⟩ := pts_equiv k B
  obtain ⟨hfree, hfin, -⟩ := tl_free_finrank k l hlk B
  have hc : ∀ n : ℕ, Nat.card {x : B.Pt // x ^ (l ^ n) = 1} = l ^ (2 * B.dim * n) := by
    intro n
    rw [card_torsion_pt k B (l ^ n) (by push_cast; exact pow_ne_zero _ hlk), ← pow_mul, mul_comm n]
  let E : ℕ → L →+ Additive B.Pt := fun j =>
    AddMonoidHom.mk' (fun x => Additive.ofMul (e (ev j x))) fun x y => by
      rw [hadd, map_mul]; rfl
  have hE : ∀ j (n : ℕ) x, e (ev j (n • x)) = e (ev j x) ^ n := fun j n x =>
    congrArg Additive.toMul (map_nsmul (E j) n x)
  have key : ∀ j : ℕ, (LinearMap.charpoly φ).map (Int.castRingHom (ZMod (l ^ j))) =
      (LinearMap.charpoly (tend l B f)).map (PadicInt.toZModPow j) := by
    intro j
    haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ hl.ne_zero⟩
    let K := (powMonoidHom (l ^ j) : B.Pt →* B.Pt).ker
    have hK : ∀ x : B.Pt, x ∈ K ↔ x ^ (l ^ j) = 1 := fun x => MonoidHom.mem_ker
    letI : Module (ZMod (l ^ j)) (Additive K) := AddCommGroup.zmodModule fun x =>
      congrArg Additive.ofMul (Subtype.ext (by
        change ((Additive.toMul x : K) : B.Pt) ^ (l ^ j) = 1
        exact (hK _).1 (Additive.toMul x).2))
    have hsm : ∀ (c : ZMod (l ^ j)) (q : Additive K), c • q = c.val • q := fun c q => by
      conv_lhs => rw [← ZMod.natCast_zmod_val c]
      exact Nat.cast_smul_eq_nsmul _ _ _
    have hπ : ((l : ZMod (l ^ j))) ^ j = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
    let G0 : Additive K →+ Additive K := AddMonoidHom.mk'
      (fun q => Additive.ofMul ⟨((Additive.toMul q : K) : B.Pt) ≫ f.hom, (hK _).2 (by
        rw [← ptMap_apply, ← map_pow, (hK _).1 (Additive.toMul q).2, map_one])⟩)
      fun q q' => congrArg Additive.ofMul (Subtype.ext (MonObj.mul_comp _ _ _))
    let G : Additive K →ₗ[ZMod (l ^ j)] Additive K := G0.toZModLinearMap (l ^ j)
    let eL : L →+ Additive K := AddMonoidHom.mk'
      (fun x => Additive.ofMul ⟨e (ev j x), (hK _).2 (by
        rw [← hE, (hker j _).2 ⟨x, rfl⟩, map_one])⟩)
      fun x y => congrArg Additive.ofMul (Subtype.ext (by
        change e (ev j (x + y)) = e (ev j x) * e (ev j y)
        rw [hadd, map_mul]))
    let eT : Tate l B.Pt →+ Additive K := AddMonoidHom.mk'
      (fun t => Additive.ofMul ⟨t.lev j, (hK _).2 (t.lev_pow j)⟩) fun s t => rfl
    obtain ⟨_, _, h1⟩ := charpoly_reduce (Int.castRingHom (ZMod (l ^ j))) ZMod.intCast_surjective
      ((l : ℤ) ^ j) (by rw [map_pow, map_natCast, hπ]) eL
      (fun q => by
        obtain ⟨x, hx⟩ := (him j (e.symm (Additive.toMul q : K))).1 (by
          rw [← map_pow, (hK _).1 (Additive.toMul q).2, map_one])
        refine ⟨x, congrArg Additive.ofMul (Subtype.ext ?_)⟩
        change e (ev j x) = _
        rw [hx, MulEquiv.apply_symm_apply]
        rfl)
      (fun r x => by rw [map_zsmul, eq_intCast, Int.cast_smul_eq_zsmul])
      (fun x hx => by
        have h0 : e (ev j x) = 1 := congrArg Subtype.val (congrArg Additive.toMul hx)
        obtain ⟨y, hy⟩ := (hker j x).1 ((map_eq_one_iff e e.injective).1 h0)
        exact ⟨y, by rw [hy, ← Nat.cast_pow, natCast_zsmul]⟩)
      φ G (fun x => congrArg Additive.ofMul (Subtype.ext (by
        change e (ev j (φ x)) = e (ev j x) ≫ f.hom
        rw [hequi, he])))
    obtain ⟨_, _, h2⟩ := charpoly_reduce (PadicInt.toZModPow j) (ZMod.ringHom_surjective _)
      ((l : ℤ_[l]) ^ j) (by rw [map_pow, map_natCast, hπ]) eT
      (fun q => by
        obtain ⟨t, ht⟩ := tate_lev_surj B.Pt l (2 * B.dim) hc j _ ((hK _).1 (Additive.toMul q).2)
        exact ⟨t, congrArg Additive.ofMul (Subtype.ext ht)⟩)
      (fun a t => by
        rw [hsm]
        rfl)
      (fun t ht => by
        obtain ⟨s, hs⟩ := (tate_lev_eq_one_iff B.Pt l t j).1
          (congrArg Subtype.val (congrArg Additive.toMul ht))
        exact ⟨s, hs⟩)
      (tend l B f) G (fun t => rfl)
    exact h1.symm.trans h2
  have hT := (charpoly_tate_det_trace k l hlk B f).2.1
  have hinj : Function.Injective (Polynomial.map (Int.castRingHom ℤ_[l])) :=
    Polynomial.map_injective _ Int.cast_injective
  apply hinj
  rw [show Int.castRingHom ℤ_[l] = algebraMap ℤ ℤ_[l] from RingHom.ext_int _ _, hT]
  ext i
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  have h := congrArg (fun P => Polynomial.coeff P i) (key n)
  simp only [Polynomial.coeff_map, eq_intCast] at h ⊢
  rw [map_intCast]
  exact h

end GlobalTheory.AV.AbVar
