import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomCompEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureLocalPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianLocalPointDivisibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteHopfPointsSeparateStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff.LevKer

attribute [local instance] GlobalTheory.HopfShear.pointsGroup

@[reducible] def pointsCommGroup {R A X : Type} [CommRing R] [CommRing A] [CommRing X] [HopfAlgebra R A] [IsCocomm R A]
    [Algebra R X] : CommGroup (WithConv (A →ₐ[R] X)) :=
  { GlobalTheory.HopfShear.pointsGroup with mul_comm := mul_comm }

attribute [local instance] pointsCommGroup

section
variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {N : ℕ}
  {A : Type} [CommRing A] [HopfAlgebra R A]

def ptHom (θ : TorsPt G N A) (B : Type) [CommRing B] [Algebra R B] : Tors G N B →* WithConv (A →ₐ[R] B) :=
  MonoidHom.mk' (fun z => toConv (θ.pt B z)) (θ.mul B)

theorem ptHom_apply (θ : TorsPt G N A) (B : Type) [CommRing B] [Algebra R B] (z : Tors G N B) :
    ptHom θ B z = toConv (θ.pt B z) := rfl

theorem ptHom_torsMap (θ : TorsPt G N A) {B C : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
    (φ : B →ₐ[R] C) (z : Tors G N B) : ptHom θ C (torsMap φ z) = ptsPush A φ (ptHom θ B z) :=
  congrArg toConv (θ.nat B C φ z)

theorem ptHom_injective {K : Type} [Field K] [Algebra R K] {θ : TorsPt G N A} (h : IsLevel K θ)
    (B : Type) [CommRing B] [Algebra R B] : Function.Injective (ptHom θ B) := by
  obtain ⟨V, hV⟩ := h.opn
  intro x y hxy
  exact (hV B).injOn trivial trivial (congrArg ofConv hxy)

theorem tors_pow_val {B : Type} [CommRing B] [Algebra R B] (z : Tors G N B) (n : ℕ) : (z ^ n).1 = z.1 ^ n := rfl

theorem tors_pow_self {B : Type} [CommRing B] [Algebra R B] (z : Tors G N B) : z ^ N = 1 := Subtype.ext z.2

theorem range_subset_of_local {S B : Type} [CommRing S] [IsLocalRing S] [CommRing B] [IsLocalRing B] (f : A →+* S)
    (j : S →+* B) [IsLocalHom j] (V : (Sp A).Opens) (h : Set.range (spMap (j.comp f)) ⊆ V) :
    Set.range (spMap f) ⊆ V := by
  have h0 : PrimeSpectrum.comap (j.comp f) (IsLocalRing.closedPoint B) ∈ V := h ⟨IsLocalRing.closedPoint B, rfl⟩
  rw [PrimeSpectrum.comap_comp_apply, IsLocalRing.comap_closedPoint] at h0
  rintro _ ⟨x, rfl⟩
  have hs := (IsLocalRing.specializes_closedPoint (R := S) x).map (PrimeSpectrum.continuous_comap f)
  exact hs.mem_open V.isOpen h0

end

section
variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {N m : ℕ}
  {A : Type} [CommRing A] [HopfAlgebra R A] {A' : Type} [CommRing A'] [HopfAlgebra R A']
  {θ : TorsPt G N A} {θ' : TorsPt G (N * m) A'} {g : A' →ₐc[R] A}

theorem exists_ptsMap_of_tors
    (hg : ∀ (B : Type) [CommRing B] [Algebra R B] (z : Tors G N B),
      θ'.pt B (torsIncl (Dvd.intro m rfl) z) = (θ.pt B z).comp (g : A' →ₐ[R] A))
    {B : Type} [CommRing B] [Algebra R B] (z : Tors G (N * m) B) (hz : z ^ N = 1) :
    ∃ ψ, ptHom θ' B z = pointsMap B g ψ :=
  ⟨ptHom θ B ⟨z.1, congrArg Subtype.val hz⟩, congrArg toConv (hg B ⟨z.1, congrArg Subtype.val hz⟩)⟩

end

theorem ptsPush_injective {R A B C : Type} [CommRing R] [CommRing A] [Bialgebra R A] [CommRing B] [Algebra R B]
    [CommRing C] [Algebra R C] (φ : B →ₐ[R] C) (h : Function.Injective φ) : Function.Injective (ptsPush A φ) :=
  fun x y hxy => ofConv_injective (AlgHom.ext fun a => h (DFunLike.congr_fun (congrArg ofConv hxy) a))

theorem ptsPush_ptsPush {R A B C D : Type} [CommRing R] [CommRing A] [Bialgebra R A] [CommRing B] [Algebra R B]
    [CommRing C] [Algebra R C] [CommRing D] [Algebra R D] (φ : B →ₐ[R] C) (ψ : C →ₐ[R] D) (x : WithConv (A →ₐ[R] B)) :
    ptsPush A ψ (ptsPush A φ x) = ptsPush A (ψ.comp φ) x := rfl

theorem ptsPush_ofId {R A C D : Type} [CommRing R] [CommRing A] [Bialgebra R A]
    [CommRing C] [Algebra R C] [CommRing D] [Algebra R D] (ψ : C →ₐ[R] D) (x : WithConv (A →ₐ[R] R)) :
    ptsPush A ψ (ptsPush A (Algebra.ofId R C) x) = ptsPush A (Algebra.ofId R D) x := by
  rw [ptsPush_ptsPush, Subsingleton.elim (ψ.comp (Algebra.ofId R C)) (Algebra.ofId R D)]

theorem ptsPush_ptsMap {R A A' C D : Type} [CommRing R] [CommRing A] [Bialgebra R A] [CommRing A'] [Bialgebra R A']
    [CommRing C] [Algebra R C] [CommRing D] [Algebra R D] (ψ : C →ₐ[R] D) (g : A' →ₐc[R] A) (x : WithConv (A →ₐ[R] C)) :
    ptsPush A' ψ (pointsMap C g x) = pointsMap D g (ptsPush A ψ x) := rfl

theorem exists_ptsMap_of_local (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K]
    [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (N m : ℕ) (hN : N ≠ 0) (hm : m ≠ 0)
    (A : Type) [CommRing A] [HopfAlgebra R A] [Module.Finite R A]
    (A' : Type) [CommRing A'] [HopfAlgebra R A'] [IsCocomm R A'] [Module.Finite R A'] [Module.Projective R A']
    (θ : TorsPt G N A) (θ' : TorsPt G (N * m) A') (h' : IsLevel K θ') (g : A' →ₐc[R] A)
    (hg : ∀ (B : Type) [CommRing B] [Algebra R B] (z : Tors G N B),
      θ'.pt B (torsIncl (Dvd.intro m rfl) z) = (θ.pt B z).comp (g : A' →ₐ[R] A))
    (B : Type) [CommRing B] [Algebra R B] [IsLocalRing B] (φ : WithConv (A' →ₐ[R] B)) (hφ : φ ^ N = 1) :
    ∃ ψ, φ = pointsMap B g ψ := by
  obtain ⟨z, s₀, hz⟩ := GlobalTheory.T.level_structure_local_points R K G hG (N * m) (mul_ne_zero hN hm) A' θ' h' B φ.ofConv
  let s : WithConv (A' →ₐ[R] R) := toConv s₀
  replace hz : φ = ptHom θ' B z * ptsPush A' (Algebra.ofId R B) s := hz
  have hRK : Function.Injective (Algebra.ofId R K) := IsFractionRing.injective R K
  have hs : s ^ (N * m) = 1 := by
    apply ptsPush_injective _ hRK
    obtain ⟨w, hw⟩ := h'.gen.2 (ptsPush A' (Algebra.ofId R K) s).ofConv
    have hw' : ptHom θ' K w = ptsPush A' (Algebra.ofId R K) s := congrArg toConv hw
    rw [map_pow, ← hw', ← map_pow, tors_pow_self, map_one, map_one]
  let q : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R B) (IsLocalRing.closedPoint B)
  let S := Localization.AtPrime q.asIdeal
  have hu : ∀ y : q.asIdeal.primeCompl, IsUnit (Algebra.ofId R B y) := fun y =>
    (IsLocalRing.notMem_maximalIdeal.1 y.2)
  let j : S →ₐ[R] B := IsLocalization.liftAlgHom hu
  have hj : IsLocalHom (j : S →+* B) := ⟨fun a ha => by
    obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl a
    rw [IsLocalization.AtPrime.isUnit_mk'_iff S q.asIdeal]
    have h1 : (j : S →+* B) (IsLocalization.mk' S x y) * algebraMap R B y = algebraMap R B x := by
      rw [← j.commutes, ← j.commutes, RingHom.coe_coe, ← map_mul, IsLocalization.mk'_spec]
    exact IsLocalRing.notMem_maximalIdeal.2 (h1 ▸ ha.mul (hu y))⟩
  have huK : ∀ y : q.asIdeal.primeCompl, IsUnit (Algebra.ofId R K y) := fun y =>
    IsUnit.mk0 _ fun h0 => y.2 (by rw [hRK (h0.trans (map_zero _).symm)]; exact q.asIdeal.zero_mem)
  let i : S →ₐ[R] K := IsLocalization.liftAlgHom huK
  have hi : Function.Injective i := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl a
    have h1 : i (IsLocalization.mk' S x y) * algebraMap R K y = algebraMap R K x := by
      rw [← i.commutes, ← i.commutes, ← map_mul, IsLocalization.mk'_spec]
    rw [ha, zero_mul] at h1
    have hx : x = 0 := hRK (h1.symm.trans (map_zero _).symm)
    simp [hx]
  let sS := ptsPush A' (Algebra.ofId R S) s
  have hsB : ptsPush A' j sS = ptsPush A' (Algebra.ofId R B) s := ptsPush_ofId j s
  have ht : ptsPush A' j (sS ^ N) = ptHom θ' B (z⁻¹ ^ N) := by
    rw [map_pow, hsB, map_pow, map_inv, inv_pow, eq_inv_iff_mul_eq_one, ← mul_pow, mul_comm, ← hz, hφ]
  obtain ⟨V, hV⟩ := h'.opn
  obtain ⟨h, -, hh⟩ := (hV S).surjOn (a := (sS ^ N).ofConv) (range_subset_of_local _ (j : S →+* B) V (by
    have := (hV B).mapsTo (x := z⁻¹ ^ N) trivial
    rw [show θ'.pt B (z⁻¹ ^ N) = j.comp (sS ^ N).ofConv from (congrArg ofConv ht).symm] at this
    exact this))
  replace hh : ptHom θ' S h = sS ^ N := congrArg toConv hh
  have hhm : h ^ m = 1 := ptHom_injective h' S (by
    rw [map_pow, hh, ← pow_mul, ← map_pow, hs, map_one, map_one])
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.semiabelian_local_point_divisible R K G hG q h.1 N hN
  let y : Tors G (N * m) S := ⟨y₀, by rw [pow_mul, hy₀]; exact congrArg Subtype.val hhm⟩
  have hy : y ^ N = h := Subtype.ext hy₀
  let u := sS * (ptHom θ' S y)⁻¹
  have huN : u ^ N = 1 := by
    rw [mul_pow, inv_pow, ← map_pow (ptHom θ' S), hy, hh, mul_inv_cancel]
  obtain ⟨ψ₁, hψ₁⟩ : ∃ ψ, u = pointsMap S g ψ := by
    obtain ⟨v, hv⟩ := h'.gen.2 (ptsPush A' i u).ofConv
    replace hv : ptHom θ' K v = ptsPush A' i u := congrArg toConv hv
    obtain ⟨χ, hχ⟩ := exists_ptsMap_of_tors hg v (ptHom_injective h' K (by
      rw [map_pow, hv, ← map_pow, huN, map_one, map_one]))
    obtain ⟨c, hc⟩ := exists_algHom_comp_eq (A := R) (K := K) χ.ofConv
    refine ⟨ptsPush A (Algebra.ofId R S) (toConv c), ptsPush_injective i hi ?_⟩
    rw [← hv, hχ, ptsPush_ptsMap, ptsPush_ofId]
    exact congrArg (fun x => pointsMap K g (toConv x)) hc.symm
  have hφ' : φ = ptHom θ' B (z * torsMap j y) * ptsPush A' j u := by
    rw [hz, map_mul, ptHom_torsMap, map_mul, map_inv, hsB, _root_.mul_assoc, mul_comm (ptsPush A' _ s), mul_inv_cancel_left]
  obtain ⟨ψ₂, hψ₂⟩ := exists_ptsMap_of_tors hg (z * torsMap j y) (ptHom_injective h' B (by
    rw [hφ', mul_pow, ← map_pow (ptsPush A' j), huN, map_one, _root_.mul_one] at hφ
    rw [map_pow, hφ, map_one]))
  exact ⟨ψ₂ * ptsPush A j ψ₁, by rw [hφ', hψ₂, hψ₁, ptsPush_ptsMap, map_mul]⟩

theorem ker_eq_torsionIdeal : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N m : ℕ), N ≠ 0 → m ≠ 0 → ∀ (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A] (A' : Type) [CommRing A'] [HopfAlgebra R A'] [IsCocomm R A'] [Module.Finite R A'] [Module.Projective R A'] (θ : TorsPt G N A) (θ' : TorsPt G (N * m) A'), IsLevel K θ → IsLevel K θ' → ∀ g : A' →ₐc[R] A, (∀ (B : Type) [CommRing B] [Algebra R B] (z : Tors G N B), θ'.pt B (torsIncl (Dvd.intro m rfl) z) = (θ.pt B z).comp (g : A' →ₐ[R] A)) → RingHom.ker (g : A' →ₐ[R] A) = torsionIdeal R A' N := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N m hN hm A _ _ _ _ _ A' _ _ _ _ _ θ θ' h h' g hg
  refine le_antisymm ?_ fun a ha => ?_
  · intro a ha
    let Q := A' ⧸ torsionIdeal R A' N
    let π : A' →ₐ[R] Q := Ideal.Quotient.mkₐ R _
    have hπ : toConv π ^ N = 1 :=
      (torsionIdeal_le_ker_iff N π).1 fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
    refine Ideal.Quotient.eq_zero_iff_mem.1 (show π a = 0 from ?_)
    refine Module.eq_zero_of_localization_maximal (R := Q) (fun P _ => Localization.AtPrime P)
      (fun P _ => Algebra.linearMap Q (Localization.AtPrime P)) _ fun P _ => ?_
    let l := IsScalarTower.toAlgHom R Q (Localization.AtPrime P)
    obtain ⟨ψ, hψ⟩ := exists_ptsMap_of_local R K G hG N m hN hm A A' θ θ' h' g hg (Localization.AtPrime P)
      (ptsPush A' l (toConv π)) (by rw [← map_pow, hπ, map_one])
    have h1 : l (π a) = ψ.ofConv ((g : A' →ₐ[R] A) a) := DFunLike.congr_fun (congrArg ofConv hψ) a
    rw [RingHom.mem_ker.1 ha, map_zero] at h1
    exact h1
  · refine (GlobalTheory.T.finite_hopf_points_separate R K A).2.1 _ fun ψ => ?_
    obtain ⟨w, rfl⟩ := h.gen.2 ψ
    refine (torsionIdeal_le_ker_iff N ((θ.pt K w).comp (g : A' →ₐ[R] A))).2 ?_ ha
    change pointsMap K g (ptHom θ K w) ^ N = 1
    rw [← map_pow, ← map_pow, tors_pow_self, map_one, map_one]

end GlobalTheory.GroupBplus.Aff.LevKer
