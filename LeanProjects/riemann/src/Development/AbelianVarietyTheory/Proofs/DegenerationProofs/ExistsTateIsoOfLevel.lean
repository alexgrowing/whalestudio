import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTateIsoZetaEq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.Ex.ThetaDescent

theorem nonempty_algHom (K A : Type) [Field K] [IsAlgClosed K] [CommRing A] [Nontrivial A] [Algebra K A]
    [Algebra.FiniteType K A] : Nonempty (A →ₐ[K] K) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  letI := Ideal.Quotient.field M
  haveI : Module.Finite K (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ M)
  exact ⟨(IsAlgClosed.lift : (A ⧸ M) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K M)⟩

theorem exists_retract {F R K κ : Type} [CommRing F] [CommRing R] [Field K] [IsAlgClosed K] [Field κ] (g : F →+* R)
    (hg : g.FiniteType) (b : F →+* K) (i : K →+* κ) (φ : R →+* κ) (hφ : φ.comp g = i.comp b) (u : κˣ) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (j : A →+* κ) (s : A →+* K) (k : K →+* A) (ψ : R →+* A) (u' : Aˣ),
      Function.Injective j ∧ j.comp ψ = φ ∧ j.comp k = i ∧ (∀ x, s (k x) = x) ∧ j u' = u := by
  classical
  letI := g.toAlgebra
  letI := i.toAlgebra
  obtain ⟨t, ht⟩ := hg.out
  let A : Subalgebra K κ := Algebra.adjoin K ((insert (u : κ) (insert ((u⁻¹ : κˣ) : κ) (t.image φ)) : Finset κ) : Set κ)
  haveI : Algebra.FiniteType K A := (Subalgebra.fg_iff_finiteType _).1 ⟨_, rfl⟩
  have hA : ∀ r, φ r ∈ A := fun r => by
    have hr : r ∈ Algebra.adjoin F (t : Set R) := ht ▸ Algebra.mem_top
    induction hr using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (by simp only [Finset.coe_insert, Finset.coe_image]; exact Or.inr (Or.inr ⟨x, hx, rfl⟩))
    | algebraMap x => exact (RingHom.congr_fun hφ x).symm ▸ A.algebraMap_mem (b x)
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  obtain ⟨s⟩ := nonempty_algHom K A
  have h₁ : (u : κ) ∈ A := Algebra.subset_adjoin (by simp)
  have h₂ : ((u⁻¹ : κˣ) : κ) ∈ A := Algebra.subset_adjoin (by simp)
  refine ⟨A, inferInstance, inferInstance, A.val.toRingHom, s.toRingHom, algebraMap K A,
    φ.codRestrict A hA, ⟨⟨_, h₁⟩, ⟨_, h₂⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩, Subtype.val_injective, rfl, rfl,
    s.commutes, rfl⟩

theorem exists_embedding {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (F : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ F] (h : H.rt0 ∈ F) {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (ρ : K)
    (hρ : ρ ^ 2 = -(H.d : K)) : ∃ b : F →+* K, b ⟨_, h⟩ = ρ := by
  have hi : Irreducible (Polynomial.X ^ 2 - Polynomial.C (-(H.d : ℚ))) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b hb => by
      have : (0 : ℚ) < H.d := by exact_mod_cast H.d_prime.pos
      nlinarith [sq_nonneg b]
  have hm : Polynomial.X ^ 2 - Polynomial.C (-(H.d : ℚ)) = minpoly ℚ (⟨_, h⟩ : F) :=
    minpoly.eq_of_irreducible_of_monic hi (by
      apply Subtype.ext
      simp [H.sqrt_neg_disc_sq]) (Polynomial.monic_X_pow_sub_C _ two_ne_zero)
  obtain ⟨b, hb⟩ := IntermediateField.exists_algHom_of_splits_of_aeval (F := ℚ) (E := F) (K := K)
    (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) (x := ⟨_, h⟩) (y := ρ) (by rw [← hm]; simp [hρ])
  exact ⟨b.toRingHom, hb⟩

theorem exists_tateIso_of_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    (l : Geo.Tor.Level H) {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : TateIso D k Q act e) {N : ℕ} (hN : 0 < N)
    (he : ∀ x y c c', x ^ N = 1 → y ^ N = 1 → e N x y c → e N x y c' → c = c') (z : kˣ) (hz : IsPrimitiveRoot z N)
    (x : D.La → Q) (hadd : ∀ a b, x (a + b) = x a * x b) (hlin : ∀ (c : 𝓞 E) a, x (c • a) = act c (x a))
    (hpow : ∀ a, x a ^ N = 1) (hiso : ∀ a b, e N (x a) (x b) (z ^ D.EF a b)) :
    ∃ J : TateIso D k Q act e, J.ζ N = z ∧ ∀ a, J.ev N a = x a := by
  obtain ⟨I, hI⟩ := GlobalTheory.TateRoot.exists_tateIso_zeta_eq E H D l k Q act e I N z hN (IsPrimitiveRoot.coe_units_iff.2 hz)
  replace hI : I.ζ N = z := Units.ext hI
  have := D.fin
  have := D.proj
  choose f₀ hf₀ using fun a => (I.onto N hN (x a)).1 (hpow a)
  let M : Submodule (𝓞 E) D.La := LinearMap.range ((N : 𝓞 E) • LinearMap.id)
  have hM : ∀ a b, M.mkQ a = M.mkQ b ↔ I.ev N a = I.ev N b := fun a b => by
    have e₁ : I.ev N a = I.ev N (a - b) * I.ev N b := by rw [← I.add, sub_add_cancel]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, e₁, mul_eq_right, I.ker N hN]
    exact exists_congr fun c => by simp [Nat.cast_smul_eq_nsmul, eq_comm]
  let g₀ : D.La →ₗ[𝓞 E] D.La ⧸ M :=
    { toFun := fun a => M.mkQ (f₀ a)
      map_add' := fun a b => by rw [← map_add, hM, I.add, hf₀, hf₀, hf₀, hadd]
      map_smul' := fun c a => by rw [← map_smul, RingHom.id_apply, hM, I.lin, hf₀, hf₀, hlin] }
  obtain ⟨f, hf⟩ := Module.projective_lifting_property M.mkQ g₀ M.mkQ_surjective
  have hf' : ∀ a, I.ev N (f a) = x a := fun a => ((hM _ _).1 (LinearMap.congr_fun hf a)).trans (hf₀ a)
  by_cases hpq : 1 ≤ D.p + D.q
  · obtain ⟨g, hg, hν⟩ := GlobalTheory.exists_sim_lift E H D N f 1 hN isCoprime_one_left fun a b => by
      have h₁ := I.isom N hN (f a) (f b)
      rw [hf', hf', hI] at h₁
      have h₂ := he _ _ _ _ (hpow a) (hpow b) h₁ (hiso a b)
      rw [_root_.one_mul, ← hz.zpow_eq_one_iff_dvd, zpow_sub, h₂, mul_inv_cancel]
    refine ⟨GlobalTheory.LevelTwist.twist I g ((GlobalTheory.SimAlg.sim_group E H D hpq).1 g), ?_, fun a => ?_⟩
    · rw [GlobalTheory.LevelTwist.twist_ζ, GlobalTheory.LevelTwist.zeta_zpow_congr I hN hν, zpow_one, hI]
    · rw [GlobalTheory.LevelTwist.twist_ev, GlobalTheory.LevelTwist.ev_congr I hN (hg a), hf']
  · have : Subsingleton D.La := Module.finrank_zero_iff.1 (D.rank.trans (by omega))
    exact ⟨I, hI, fun a => by rw [← hf', Subsingleton.elim (f a) a]⟩

theorem isThetaPt_unit_mul {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A))
    (v v' : I → Γ(T.left, ⊤)) (c : Γ(T.left, ⊤)) (hc : IsUnit c) (hv : ∀ i, v' i = c * v i)
    (h : IsThetaPt P k x v) : IsThetaPt P k x v' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hp, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h3 p
  have hc1 : IsUnit (show Γ((overRes V).left, ⊤) from V.ι.appTop.hom c) := hc.map V.ι.appTop.hom
  obtain ⟨c', hc'⟩ := hc1
  refine ⟨V, hp, th, s1, α, τ, U, s2, w, c' * u, a1, a2, a3, a4, a5, a6, a7, fun i => ?_⟩
  have e1 : (show Γ((overRes V).left, ⊤) from V.ι.appTop.hom (v' i)) =
      (show Γ((overRes V).left, ⊤) from V.ι.appTop.hom c) * (show Γ((overRes V).left, ⊤) from V.ι.appTop.hom (v i)) := by
    rw [hv i]
    exact map_mul V.ι.appTop.hom c (v i)
  have e2 : (show Γ((overRes V).left, ⊤) from V.ι.appTop.hom (v i)) = u * w i := a8 i
  rw [← hc', e2, ← _root_.mul_assoc] at e1
  exact e1

theorem exists_affine (hG : GlobalFnsSt) (hB : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) (k : ℕ)
    (hk : Odd k) (hu : IsUnit (k : Γ(S, ⊤))) {T : Over S} {I : Type} (y : I → (T ⟶ P.A)) (hf : (Set.range y).Finite)
    (hy : ∀ i, y i ^ (k ^ 2) = 1) (p : T.left) :
    ∃ (W : T.left.Opens) (hW : IsAffineOpen W) (x : Sp Γ(T.left, W) ⟶ S) (r : Over.mk x ⟶ T), p ∈ W ∧
      r.left = hW.fromSpec ∧ ∃ v, IsThetaPt P k (fun a => r ≫ y a) v := by
  have cg := GlobalTheory.AbLaw.CubeAssembly.cube_gen
  have neg := GlobalTheory.exists_gen_negLB hG
  obtain ⟨α₀, hα₀⟩ := (GlobalTheory.MulPull.mulPull_of_cube_of_symm cg neg).1 S P k
  have sym := (GlobalTheory.symLift_odd hG (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube cg).1).2.2 neg).1
  obtain ⟨V₀, hV₀, b, hb⟩ := hB S P 1 le_rfl (T.hom p)
  haveI := hf.to_subtype
  choose V hV θ hθ using fun i : Set.range y =>
    (sym S P (k ^ 2) hk.pow T i.1 (by obtain ⟨_, j, rfl⟩ := i; exact hy j)).1 p
  let O : T.left.Opens := T.hom ⁻¹ᵁ V₀ ⊓ ⟨⋂ i, (V i).carrier, isOpen_iInter_of_finite fun i => (V i).2⟩
  have hO : p ∈ O := ⟨hV₀, Set.mem_iInter.2 hV⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hWO⟩ := T.left.isBasis_affineOpens.exists_subset_of_mem_open hO O.2
  have hW' : IsAffineOpen W := hW
  let x₀ : Sp Γ(T.left, W) ⟶ T.left := hW'.fromSpec
  have hx₀ : Set.range x₀ = W := hW'.range_fromSpec
  obtain ⟨t, ht⟩ : ∃ t : Sp Γ(T.left, W) ⟶ V₀.toScheme, t ≫ V₀.ι = x₀ ≫ T.hom :=
    ⟨IsOpenImmersion.lift V₀.ι (x₀ ≫ T.hom) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨q, rfl⟩
      exact (hWO (hx₀.le ⟨q, rfl⟩)).1), IsOpenImmersion.lift_fac _ _ _⟩
  have ex : t ≫ (overRes (T := baseOver S) V₀).hom = x₀ ≫ T.hom := (congrArg (t ≫ ·) (Category.comp_id _)).trans ht
  let r : baseAt t ⟶ T := Over.homMk x₀ ex.symm
  refine ⟨W, hW', t ≫ (overRes (T := baseOver S) V₀).hom, r, hpW, rfl, ?_⟩
  obtain ⟨-, hsp⟩ := hb _ t (fun i => VVRank.pullS P.A _ (homAt t) (b i)) fun i => VVRank.isPullSec_pullS _ _ _ _
  haveI : Subsingleton (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  obtain ⟨th, hth⟩ := ThetaLocal.exists_generator _ hsp
  refine ThetaLocal.exists_isThetaPt P k hk α₀ hα₀ (T := baseAt t) ?_ _ th hth fun i => ?_
  · simpa using hu.map (baseAt t).hom.appTop.hom
  · let i' : Set.range y := ⟨_, i, rfl⟩
    obtain ⟨u, hu'⟩ : ∃ u : Sp Γ(T.left, W) ⟶ (V i').toScheme, u ≫ (V i').ι = x₀ :=
      ⟨IsOpenImmersion.lift (V i').ι x₀ (by
        rw [hx₀, Scheme.Opens.range_ι]; exact fun q hq => Set.mem_iInter.1 (hWO hq).2 i'), IsOpenImmersion.lift_fac _ _ _⟩
    let r' : baseAt t ⟶ overRes (V i') := Over.homMk u
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ T.hom) hu').trans ex.symm))
    obtain ⟨θ', hθ'⟩ := GlobalLift.exists_symLift_pull P.isLB r' (hθ i')
    have e : r' ≫ overResι (V i') = r := Over.OverMorphism.ext hu'
    rw [← Category.assoc, e] at hθ'
    rw [← Nat.cast_pow]
    exact ⟨θ', hθ'⟩

theorem finite_range {La Q : Type} [AddCommGroup La] [Module.Finite ℤ La] [Group Q] {N : ℕ} (hN : N ≠ 0) (x : La → Q)
    (hadd : ∀ a b, x (a + b) = x a * x b) (hpow : ∀ a, x a ^ N = 1) : (Set.range x).Finite := by
  let φ : La →+ Additive Q := AddMonoidHom.mk' (fun a => Additive.ofMul (x a)) hadd
  let M : Submodule ℤ La := φ.ker.toIntSubmodule
  have hM : ∀ a, a ∈ M ↔ φ a = 0 := fun _ => Iff.rfl
  haveI : Finite (La ⧸ M) := Module.finite_of_fg_torsion _ fun q => by
    obtain ⟨a, rfl⟩ := M.mkQ_surjective q
    refine ⟨⟨(N : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN)⟩, ?_⟩
    change M.mkQ ((N : ℤ) • a) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hM, natCast_zsmul, map_nsmul]
    exact hpow a
  refine (Set.finite_range fun q : La ⧸ M => x q.out).subset ?_
  rintro _ ⟨a, rfl⟩
  refine ⟨M.mkQ a, ?_⟩
  have h : (M.mkQ a).out - a ∈ M := (Submodule.Quotient.eq M).1 (Quotient.out_eq _)
  have e : (M.mkQ a).out = ((M.mkQ a).out - a) + a := (sub_add_cancel _ _).symm
  have h' : x ((M.mkQ a).out - a) = 1 := h
  show x _ = _
  rw [e, hadd, h', _root_.one_mul]

abbrev fnA {A : Type} [CommRing A] (x : A) : Γ(Sp A, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x

theorem appTop_fnA {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : A) :
    (spMap f).appTop.hom (fnA x) = fnA (f x) :=
  (congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

theorem fnA_bijective (A : Type) [CommRing A] : Function.Bijective (fnA (A := A)) :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv

theorem appTop_injective {A B : Type} [CommRing A] [CommRing B] {f : A →+* B} (hf : Function.Injective f) :
    Function.Injective (spMap f).appTop.hom := fun a b h => by
  obtain ⟨a, rfl⟩ := (fnA_bijective A).2 a
  obtain ⟨b, rfl⟩ := (fnA_bijective A).2 b
  rw [appTop_fnA, appTop_fnA] at h
  rw [hf ((fnA_bijective B).1 h)]

theorem exists_spread (hG : GlobalFnsSt) (hB : SecBaseChangeAnySt) {F K κ : Type} [Field F] [Field K] [IsAlgClosed K]
    [Field κ] {S : Scheme.{0}} (sF : S ⟶ Sp F) [LocallyOfFiniteType sF] (P : PolAV S) (b : F →+* K) (i : K →+* κ)
    (y : Sp κ ⟶ S) (hy : y ≫ sF = spMap (i.comp b)) {La : Type} [AddCommGroup La] [Module.Free ℤ La]
    [Module.Finite ℤ La] (m : ℕ) (hm : Odd m) (hu : IsUnit (m : Γ(S, ⊤))) (x : La → (Over.mk y ⟶ P.A))
    (hadd : ∀ a c, x (a + c) = x a * x c) (hpow : ∀ a, x a ^ m ^ 2 = 1) (v : La → K)
    (hv : IsThetaPt P m x fun a => fnOf (i (v a))) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (j : A →+* κ) (s : A →+* K) (k : K →+* A) (t : Sp A ⟶ S)
      (J : Over.mk y ⟶ Over.mk t) (xA : La → (Over.mk t ⟶ P.A)), Function.Injective j ∧ j.comp k = i ∧
      (∀ x, s (k x) = x) ∧ J.left = spMap j ∧ t ≫ sF = spMap (k.comp b) ∧ (∀ a, J ≫ xA a = x a) ∧
      IsThetaPt P m xA fun a => fnA (k (v a)) := by
  haveI := P.isAb.comm
  obtain ⟨Z, et, hfin, -, eadd, epow, huniv⟩ := GlobalTheory.exists_finiteEtale_latticeTorsionHom S P.A (m ^ 2) La P.isAb
    (by rw [Nat.cast_pow]; exact hu.pow 2)
  obtain ⟨h, hh, -⟩ := huniv _ x hadd hpow
  obtain ⟨W, hW, x₀, r, hp, hr, w, hw⟩ := exists_affine hG hB P m hm hu et
    (finite_range (pow_ne_zero 2 hm.pos.ne') et eadd epow) epow (h.left (IsLocalRing.closedPoint κ))
  obtain ⟨y', hy'⟩ : ∃ y' : Sp κ ⟶ Sp Γ(Z.left, W), y' ≫ hW.fromSpec = h.left :=
    ⟨IsOpenImmersion.lift hW.fromSpec h.left (by
      rw [hW.range_fromSpec]
      rintro _ ⟨q, rfl⟩
      rwa [Subsingleton.elim (α := PrimeSpectrum κ) q (IsLocalRing.closedPoint κ)]), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨φ, rfl⟩ : ∃ φ : Γ(Z.left, W) →+* κ, spMap φ = y' := ⟨(Spec.preimage y').hom, Spec.map_preimage y'⟩
  obtain ⟨g, hg⟩ : ∃ g : F →+* Γ(Z.left, W), spMap g = x₀ ≫ sF :=
    ⟨(Spec.preimage (x₀ ≫ sF)).hom, Spec.map_preimage _⟩
  have hx₀ : hW.fromSpec ≫ Z.hom = x₀ := hr ▸ Over.w r
  have hφ : spMap φ ≫ x₀ = y := by rw [← hx₀, ← Category.assoc, hy']; exact Over.w h
  have hgf : g.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := CommRingCat.ofHom g)).1 (by
    change LocallyOfFiniteType (spMap g)
    rw [hg, ← hx₀]
    infer_instance)
  have hφg : φ.comp g = i.comp b := by
    have : spMap (φ.comp g) = spMap (i.comp b) := by rw [spMap_comp, hg, ← Category.assoc, hφ, hy]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  have aff : ∀ {A : Type} [CommRing A] (t : Sp A ⟶ S), IsAffine (Over.mk t).left := fun t =>
    inferInstanceAs (IsAffine (Spec _))
  let hκ : Over.mk y ⟶ Over.mk x₀ := Over.homMk (spMap φ) hφ
  have eκ : hκ ≫ r = h := Over.OverMorphism.ext ((congrArg (spMap φ ≫ ·) hr).trans hy')
  haveI := aff x₀
  haveI := aff y
  have w₁ := ThetaBaseChange.isThetaPt_pull P hB hκ hw
  simp only [← Category.assoc, eκ, hh] at w₁
  haveI : IsLocalRing Γ((Over.mk y).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of κ)).commRingCatIsoToRingEquiv.symm.isLocalRing
  obtain ⟨u, hu₁⟩ := ThetaUniq.exists_unit_over hG P hm (ThetaUniq.isThetaPtOver_of_local P y w₁)
    (ThetaUniq.isThetaPtOver_of_local P y hv)
  obtain ⟨u₀, hu₀⟩ := (fnA_bijective κ).2 u.val
  have hne : u₀ ≠ 0 := fun h0 => u.ne_zero (hu₀.symm.trans (h0 ▸ map_zero _))
  obtain ⟨A, _, _, j, s, k, ψ, u', hj, h₁, h₂, h₃, h₄⟩ := exists_retract g hgf b i φ hφg (Units.mk0 u₀ hne)
  let hA : Over.mk (spMap ψ ≫ x₀) ⟶ Over.mk x₀ := Over.homMk (spMap ψ) rfl
  have e₁ : spMap j ≫ spMap ψ = spMap φ := by rw [← spMap_comp, h₁]
  let J : Over.mk y ⟶ Over.mk (spMap ψ ≫ x₀) := Over.homMk (spMap j) (by
    change spMap j ≫ spMap ψ ≫ x₀ = y
    rw [← Category.assoc, e₁, hφ])
  have eJ : J ≫ hA = hκ := Over.OverMorphism.ext e₁
  haveI := aff (spMap ψ ≫ x₀)
  refine ⟨A, inferInstance, inferInstance, j, s, k, _, J, fun a => hA ≫ r ≫ et a, hj, h₂, h₃, rfl, ?_, fun a => ?_, ?_⟩
  · rw [Category.assoc, ← hg, ← spMap_comp]
    congr 1
    ext c
    apply hj
    exact (RingHom.congr_fun h₁ _).trans ((RingHom.congr_fun hφg c).trans (RingHom.congr_fun h₂ _).symm)
  · rw [← Category.assoc, eJ, ← Category.assoc, eκ, hh]
  · refine isThetaPt_unit_mul P m _ _ _ (fnA u'.val) (u'.isUnit.map _) (fun a => appTop_injective hj ?_)
      (ThetaBaseChange.isThetaPt_pull P hB hA hw)
    refine (appTop_fnA j _).trans (Eq.trans ?_ (map_mul _ _ _).symm)
    refine (congrArg fnA (RingHom.congr_fun h₂ _)).trans ((hu₁ a).trans (congrArg₂ (· * ·) ?_ ?_))
    · exact hu₀.symm.trans ((congrArg fnA h₄.symm).trans (appTop_fnA j _).symm)
    · exact (congrArg (fun q => q.left.appTop.hom (w a)) eJ).symm

set_option maxHeartbeats 800000 in

theorem exists_full (hL : Laws) (hB : SecBaseChangeAnySt) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Geo.Tor.Level H} {B F K κ : Type} [CommRing B] {bs : Base l B} [Field F] [Field K] [IsAlgClosed K]
    [CharZero K] [Field κ] {S : Scheme.{0}} (sF : S ⟶ Sp F) [LocallyOfFiniteType sF] (e : B →+* F) {sB : S ⟶ Sp B}
    (hs : sB = sF ≫ spMap e) (oF : Obj D l bs sB) (b : F →+* K) (i : K →+* κ) (y : Sp κ ⟶ S)
    (hy : y ≫ sF = spMap (i.comp b)) (o' : Full D κ) (φ : o'.P.A.left ⟶ oF.t.G.left)
    (cart : IsGrpPullback o'.P.A oF.t.G y φ) (lb : LBIso o'.P.L (oF.t.PP.L.pull φ))
    (hact : letI := H.starRing; ∀ x, (o'.oa.act x).left ≫ φ = φ ≫ (oF.t.act.act x).left)
    (m : ℕ) (hm : Odd m) (z : K) (v : D.La → K) (hz : (o'.I.ζ (m ^ 2) : κ) = i z) (hv : o'.Theta m fun x => i (v x)) :
    ∃ o : Full D K, o.ρ = b (e bs.ρ) ∧ (o.I.ζ (m ^ 2) : K) = z ∧ o.Theta m v := by
  letI := H.starRing
  have hG := hL.globalFns
  have hN : 0 < m ^ 2 := pow_pos hm.pos 2
  let P := objPolAV oF
  haveI := D.fin
  haveI := D.proj
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  haveI : Module.Free ℤ D.La := inferInstance
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian sF
  haveI : IsLocallyNoetherian (Sp K) := inferInstanceAs (IsLocallyNoetherian (Spec _))
  have hu : IsUnit (m : Γ(S, ⊤)) := by
    have := ((bs.unit m hm.pos).map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom).map sB.appTop.hom
    rwa [map_natCast, map_natCast] at this
  let Φ := ObjPull.pushEquiv cart (baseOver (Sp κ))
  have p' : ∀ a, o'.I.ev (m ^ 2) a ^ m ^ 2 = 1 := fun a => (o'.I.onto _ hN _).2 ⟨a, rfl⟩
  have p'' : ∀ a, Φ (o'.I.ev (m ^ 2) a) ^ m ^ 2 = 1 := fun a => by rw [← map_pow, p', map_one]
  obtain ⟨A, _, _, j, s, k, t, J, xA, hj, hjk, hsk, hJ, ht, hx, hth⟩ := exists_spread hG hB sF P b i (𝟙 _ ≫ y)
    ((Category.assoc _ _ _).trans ((Category.id_comp _).trans hy)) m hm hu (fun a => Φ (o'.I.ev (m ^ 2) a))
    (fun a c => by rw [o'.I.add]; exact map_mul Φ _ _) p'' v
    ((ThetaPtUp.isThetaPt_iff (P₀ := P) cart lb (fun _ => rfl) p' _).1 hv)
  haveI : IsDominant (spMap j) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)⟩
  haveI := oF.proper
  have inj : ∀ p q : Over.mk t ⟶ oF.t.G, J ≫ p = J ≫ q → p = q := fun p q h => Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated (X := Sp A) oF.t.G.hom ((Over.w p).trans (Over.w q).symm) (spMap j)
      (hJ ▸ congrArg CommaMorphism.left h))
  have aadd : ∀ a c, xA (a + c) = xA a * xA c := fun a c => inj _ _ (by
    erw [MonObj.comp_mul, hx, hx, hx, o'.I.add]; exact map_mul Φ _ _)
  have apow : ∀ a, xA a ^ m ^ 2 = 1 := fun a => inj _ _ (by
    erw [MonObj.comp_pow, hx, MonObj.comp_one]; exact p'' a)
  have alin : ∀ (c : 𝓞 E) a, xA (c • a) = xA a ≫ oF.t.act.act c := fun c a => inj _ _ (by
    erw [← Category.assoc, hx, hx, o'.I.lin]
    apply Over.OverMorphism.ext
    show (_ ≫ (o'.oa.act c).left) ≫ φ = (_ ≫ φ) ≫ _
    rw [Category.assoc, hact, Category.assoc])
  have hzp : IsPrimitiveRoot z (m ^ 2) := IsPrimitiveRoot.of_map_of_injective (f := i)
    (hz ▸ IsPrimitiveRoot.coe_units_iff.2 (o'.I.ζ_prim _ hN)) i.injective
  obtain ⟨zu, rfl⟩ := hzp.isUnit hN.ne'
  have aweil : ∀ a c, WeilIs oF.t.G oF.t.PP.L (m ^ 2 : ℕ) (xA a) (xA c)
      (unitOn (Units.map k.toMonoidHom zu ^ D.EF a c)) := fun a c => by
    obtain ⟨w, hw, -⟩ := (hL.weil S P (m ^ 2) (Over.mk t)).1 _ _ (apow a) (apow c)
    have w₁ := CommPairing.weilIs_pull hG P.isAb P.isLB J hw
    rw [hx, hx] at w₁
    have w₂ := (weilIs_grpPullback_of_comm _ _ oF.t.G o'.P.A y φ _ _ oF.t.PP.isLB o'.P.isLB cart lb (baseOver _) _ _ _
      (Φ (o'.I.ev (m ^ 2) a)) (Φ (o'.I.ev (m ^ 2) c)) _ rfl rfl).1 (o'.I.isom _ hN a c)
    have w₃ := ((hL.weil S P (m ^ 2) _).1 _ _ (p'' a) (p'' c)).unique w₁ w₂
    have e₁ : o'.I.ζ (m ^ 2) = Units.map j.toMonoidHom (Units.map k.toMonoidHom zu) :=
      Units.ext (hz.trans (RingHom.congr_fun hjk _).symm)
    rw [e₁, ← map_zpow, hJ] at w₃
    have e₂ : w = unitOn (Units.map k.toMonoidHom zu ^ D.EF a c) :=
      Units.ext (appTop_injective hj ((congrArg Units.val w₃).trans (appTop_fnA j _).symm))
    exact e₂ ▸ hw
  have hsb : s.comp (k.comp b) = b := RingHom.ext fun c => hsk _
  obtain ⟨o, ⟨mp⟩⟩ := obj_pull E H D l B B bs bs (RingHom.id B) S _ sB (spMap (b.comp e)) (spMap s ≫ t) rfl rfl (by
    rw [hs, Category.assoc, ← Category.assoc t, ht, ← Category.assoc, ← spMap_comp, hsb, ← spMap_comp, ← spMap_comp,
      RingHom.comp_id]) oF
  have lb₁ : LBIso o.t.PP.L (oF.t.PP.L.pull mp.cm.F) := by
    obtain ⟨w, hw, -⟩ := mp.lin
    exact ⟨w, hw⟩
  obtain ⟨hdet, I, -⟩ := o.geom K (𝟙 _) (b.comp e) (Category.id_comp _)
  let Ψ := ObjPull.pushEquiv mp.cart (baseOver (Sp K))
  let J₀ : Over.mk (𝟙 _ ≫ spMap s ≫ t) ⟶ Over.mk t := Over.homMk (spMap s) (Category.id_comp _).symm
  let x₁ : D.La → (baseOver (Sp K) ⟶ o.t.G) := fun a => Ψ.symm (J₀ ≫ xA a)
  have hx₁ : ∀ a, (J₀ ≫ xA a).left = (x₁ a).left ≫ mp.cm.F := fun a =>
    (ObjPull.pushEquiv_symm_left mp.cart (baseOver (Sp K)) _).symm
  have p₁ : ∀ a, x₁ a ^ m ^ 2 = 1 := fun a => by
    refine (map_pow Ψ.symm _ _).symm.trans ?_
    erw [← MonObj.comp_pow, apow, MonObj.comp_one]
    exact map_one _
  obtain ⟨I₁, hI₁, hI₂⟩ := exists_tateIso_of_level l I hN
    (fun p q c c' hp hq h h' => by
      have := ((hL.weil _ (objPolAV o) (m ^ 2) _).1 _ _ hp hq).unique h h'
      exact Units.ext ((fnA_bijective K).1 (congrArg Units.val this)))
    zu (IsPrimitiveRoot.coe_units_iff.1 hzp) x₁
    (fun a c => by
      refine Eq.trans ?_ (map_mul Ψ.symm _ _)
      exact congrArg Ψ.symm ((congrArg (J₀ ≫ ·) (aadd a c)).trans (MonObj.comp_mul _ _ _)))
    (fun c a => Ψ.injective (Over.OverMorphism.ext (by
      change (x₁ _).left ≫ mp.cm.F = ((x₁ a).left ≫ (o.t.act.act c).left) ≫ mp.cm.F
      rw [Category.assoc, mp.act, ← Category.assoc, ← hx₁, ← hx₁, alin]
      rfl)))
    p₁
    (fun a c => by
      refine (weilIs_grpPullback_of_comm _ _ oF.t.G o.t.G _ mp.cm.F _ _ oF.t.PP.isLB o.t.PP.isLB mp.cart lb₁ (baseOver _)
        _ _ _ _ _ _ (hx₁ a) (hx₁ c)).2 ?_
      have w₁ := CommPairing.weilIs_pull hG P.isAb P.isLB J₀ (aweil a c)
      have e₁ : Units.map s.toMonoidHom (Units.map k.toMonoidHom zu ^ D.EF a c) = zu ^ D.EF a c := by
        rw [map_zpow]
        exact congrArg (· ^ _) (Units.ext (hsk _))
      exact (congrArg (WeilIs oF.t.G oF.t.PP.L _ _ _)
        (Units.ext ((appTop_fnA s _).trans (congrArg (fun q : Kˣ => fnA q.val) e₁)))).mp w₁)
  let oa : (objPolAV o).OAct (𝓞 E) :=
    { o.t.act.toRingAct with
      rosati := fun a _ => ⟨⊤, trivial, by
        obtain ⟨u, hu⟩ := GlobalTheory.NormRos.exists_gen_rosati o.t.PP.isLB _ _ (o.t.adj a)
        exact ⟨_, DVR.pullGen_isGen _ _ _ _ hu _⟩⟩ }
  refine ⟨⟨objPolAV o, oa, o.t.prim, b (e bs.ρ), by
    rw [← map_pow, ← map_pow, bs.ρ_sq, map_neg, map_neg, map_natCast, map_natCast], hdet, I₁, ‹_›⟩, rfl,
    congrArg Units.val hI₁, ?_⟩
  haveI : IsAffine (Over.mk t).left := inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (Over.mk (𝟙 _ ≫ spMap s ≫ t)).left := inferInstanceAs (IsAffine (Spec _))
  have w₁ := ThetaBaseChange.isThetaPt_pull P hB J₀ hth
  have e₁ : I₁.ev (m ^ 2) = x₁ := funext hI₂
  have e₂ : (fun a => J₀.left.appTop.hom (fnA (k (v a)))) = fun a => fnOf (v a) := funext fun a =>
    (appTop_fnA s _).trans (congrArg fnA (hsk _))
  rw [e₂] at w₁
  change IsThetaPt (objPolAV o) m (I₁.ev (m ^ 2)) _
  rw [e₁]
  exact (ThetaPtUp.isThetaPt_iff (P₀ := P) (P := objPolAV o) mp.cart lb₁ hx₁ p₁ _).2 w₁

end GlobalTheory.Ex.ThetaDescent
end
