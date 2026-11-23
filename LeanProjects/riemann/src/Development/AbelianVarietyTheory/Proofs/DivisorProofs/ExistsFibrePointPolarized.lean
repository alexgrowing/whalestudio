import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegDescend

theorem injective_of_charZero {n : ℕ} (hn : n ≠ 0) {k : Type} [Field k] [CharZero k] (β : cycAway n →+* k) :
    Function.Injective β := by
  have alg : ∀ x ∈ cycAway n, IsAlgebraic ℤ x := fun x hx => by
    have hle : cycAway n ≤ (Subalgebra.algebraicClosure ℤ ℂ).toSubring := by
      refine Subring.closure_le.2 ?_
      rintro _ (rfl | rfl)
      · exact ((Complex.isPrimitiveRoot_exp n hn).isIntegral (Nat.pos_of_ne_zero hn)).isAlgebraic
      · exact (isAlgebraic_natCast (R := ℤ) (A := ℂ) n).inv
    exact hle hx
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra h
  obtain ⟨x, hx, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine Ideal.comap_ne_bot_of_algebraic_mem h0 hx
    ((isAlgebraic_algHom_iff (cycAway n).subtype.toIntAlgHom Subtype.val_injective).1 (alg x x.2)) ?_
  rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  exact RingHom.injective_int _

theorem exists_factor {n : ℕ} (hn : n ≠ 0) {K k : Type} [Field K] [IsAlgClosed K] [Field k] (ι : K →+* k)
    (β : cycAway n →+* k) : ∃ β₀ : cycAway n →+* K, ι.comp β₀ = β := by
  have hk : (n : k) ≠ 0 := by simpa using ((isUnit_natCast hn).map β).ne_zero
  haveI : NeZero (n : K) := ⟨fun h => hk (by rw [← map_natCast ι, h, map_zero])⟩
  haveI : NeZero n := ⟨hn⟩
  have hle : ∀ x, β x ∈ ι.range := by
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
        obtain ⟨i, -, hi⟩ := (hz.map_of_injective ι.injective).eq_pow_of_pow_eq_one
          (isPrimitiveRoot_map hn β).pow_eq_one
        exact ⟨z ^ i, (map_pow ι _ _).trans hi⟩
      · refine ⟨(n : K)⁻¹, ?_⟩
        rw [map_inv₀, map_natCast]
        refine (eq_inv_of_mul_eq_one_left ?_).symm
        rw [← map_natCast β, ← map_mul, ← map_one β]
        exact congrArg β (Subtype.ext (by simpa using inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0)))
    | zero => exact (map_zero β).symm ▸ zero_mem _
    | one => exact (map_one β).symm ▸ one_mem _
    | add x y hx hy ihx ihy => exact (map_add β ⟨x, hx⟩ ⟨y, hy⟩).symm ▸ add_mem ihx ihy
    | neg x hx ihx => exact (map_neg β ⟨x, hx⟩).symm ▸ neg_mem ihx
    | mul x y hx hy ihx ihy => exact (map_mul β ⟨x, hx⟩ ⟨y, hy⟩).symm ▸ mul_mem ihx ihy
  let e : K ≃+* ι.range := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun x y h => ι.injective (congrArg Subtype.val h), ι.rangeRestrict_surjective⟩
  exact ⟨e.symm.toRingHom.comp (β.codRestrict _ hle), RingHom.ext fun x =>
    congrArg Subtype.val (e.apply_symm_apply (β.codRestrict _ hle x))⟩

open MonObj in

theorem exists_torsion_descend (hL : Out.Laws) {K k : Type} [Field K] [IsAlgClosed K] [Field k] [IsAlgClosed k]
    (P : Out.PolAV (Sp K)) (t : Sp k ⟶ Sp K) [Epi t] {n : ℕ} (hn : 1 ≤ n) (hK : (n : K) ≠ 0) (hk : (n : k) ≠ 0)
    (x : Over.mk t ⟶ P.A) (hx : x ^ n = 1) : ∃ x₀ : Over.mk (𝟙 (Sp K)) ⟶ P.A, x.left = t ≫ x₀.left := by
  have h₀ := (hL.mulN _ P n hn).2.2.2.2 K (𝟙 _) hK
  have h₁ := (hL.mulN _ P n hn).2.2.2.2 k t hk
  let u : Over.mk t ⟶ Over.mk (𝟙 (Sp K)) := Over.homMk t (Category.comp_id _)
  let r : {x : Over.mk (𝟙 (Sp K)) ⟶ P.A // x ^ n = 1} → {x : Over.mk t ⟶ P.A // x ^ n = 1} := fun x =>
    ⟨u ≫ x.1, by rw [← MonObj.comp_pow, x.2, MonObj.comp_one]⟩
  have hr : Function.Injective r := fun a b e => Subtype.ext (Over.OverMorphism.ext ((cancel_epi t).1
    (congrArg (fun z => z.1.left) e)))
  haveI : Finite {x : Over.mk t ⟶ P.A // x ^ n = 1} :=
    Nat.finite_of_card_ne_zero (h₁.trans_ne (pow_ne_zero _ (by omega)))
  obtain ⟨x₀, e⟩ := (hr.bijective_of_nat_card_le (h₁.trans h₀.symm).le).2 ⟨x, hx⟩
  exact ⟨x₀.1, (congrArg (fun z => z.1.left) e).symm⟩

open GlobalTheory.ZM.SiegPull in

theorem exists_point_over_subfield : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (y : Sp ℂ ⟶ F.X) (P₁ : Out.PolAV (Sp ℂ)) (α : P₁.A.left ⟶ F.univ.A.left) (α₂ : (G2 P₁.A).left ⟶ (G2 F.univ.A).left) (K : Type) [Field K] [IsAlgClosed K] (ι : K →+* ℂ) (P₀ : Out.PolAV (Sp K)) (φ₀ : P₁.A.left ⟶ P₀.A.left), 3 ≤ n → Odd n → IsGrpPullback P₁.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ P₁.A P₁.L) (F.univ.P.pull α₂) → IsPolFibre ι P₀ P₁ φ₀ → ∃ y₀ : Sp K ⟶ F.X, spMap ι ≫ y₀ = y := by
  intro g n F y P₁ α α₂ K _ _ ι P₀ φ₀ h3 _ hα sα hΛ hφ₀
  have hn : n ≠ 0 := by omega
  haveI : CharZero K := ι.charZero
  obtain ⟨β, hβ⟩ : ∃ β : cycAway n →+* ℂ, y ≫ F.s = spMap β :=
    ⟨(Spec.preimage (y ≫ F.s)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨β₀, rfl⟩ := exists_factor hn ι β
  rw [Geo.Tor.spMap_comp] at hβ
  obtain ⟨⟨c, hc⟩, hpr⟩ := siegPre_pullback g n _ _ _ _ F.s _ y F.univ rfl
  have hcp := hpr c hc F.princ
  obtain ⟨φ, φ₂, hφ, sφ, iφ, -⟩ := id hc
  obtain ⟨e, he, hα'⟩ := grpPullback_iso hφ hα
  have hψ : IsGrpPullback c.A P₀.A (spMap ι) (e.hom.left ≫ φ₀) :=
    ((Geo.Tor.isGrpPullback_of_iso e).comp hφ₀.2.1).congr (Category.id_comp _) rfl
  letI := P₀.isAb.comm
  letI := P₁.isAb.comm
  obtain ⟨ψ₂, sψ⟩ := exists_isSquare hφ₀.2.1.1.w
  have l₀ : (abelian₂ P₀.A P₀.L).IsLB := LB.isLB_linComb P₀.isLB _ _
  have l₁ : (abelian₂ P₁.A P₁.L).IsLB := LB.isLB_linComb P₁.isLB _ _
  have k₁ := SiegPull.lbIso_pull_comp hΛ (e.hom ⊗ₘ e.hom).left
  rw [isSquare_unique (isSquare_comp (isSquare_tensor e.hom) sα) sφ hα'] at k₁
  have k₂ := SiegPull.lbIso_pull_comp (lbIso_lam_pull hφ₀.2.1 hφ₀.2.2.symm sψ) (e.hom ⊗ₘ e.hom).left
  have k₃ := LBIso.trans c.isLB (pull_isLB l₁ _) (pull_isLB l₀ _)
    (LBIso.trans c.isLB (pull_isLB F.univ.isLB _) (pull_isLB l₁ _) iφ k₁.symm) k₂
  haveI : Epi (spMap ι) := ((FieldBaseChange.epi_and_isMonHom_iff K ℂ ι).1 _ _ (𝟙 _) (𝟙 _) (spMap ι)
    (IsPullback.of_vert_isIso ⟨by simp⟩)).1
  haveI : Epi ((𝟙_ (Over (Sp ℂ))).hom ≫ spMap ι) := inferInstanceAs (Epi (𝟙 _ ≫ spMap ι))
  choose lev₀ hlev₀ using fun u : Fin g ⊕ Fin g => exists_torsion_descend abelianSchemeLaws_all.1 P₀ _
    (Nat.pos_of_ne_zero hn) (Nat.cast_ne_zero.2 hn) (Nat.cast_ne_zero.2 hn)
    (pushHom hψ _ (c.lev (Pi.single u 1))) (by open MonObj in rw [← map_pow, c.lev_tors, map_one])
  obtain ⟨c₀, hc₀⟩ := exists_siegPre_of_descended_data g n _ _ K ℂ ι (spMap β₀) _ c P₀.A _ _ _ lev₀ hβ hψ
    (isSquare_comp (isSquare_tensor e.hom) sψ) l₀ k₃
    fun u => (hlev₀ u).trans (congrArg (· ≫ (lev₀ u).left) (Category.id_comp _))
  have hd : Dense {x : Sp K | ((spMap β₀) x).asIdeal = ⊥} := by
    refine dense_univ.mono fun x _ => ?_
    change Ideal.comap β₀ x.asIdeal = ⊥
    have : x.asIdeal.IsPrime := x.isPrime
    rw [Ideal.eq_bot_of_prime x.asIdeal, Ideal.comap_bot_of_injective _ (injective_of_charZero hn β₀)]
  obtain ⟨y₀, hy₀, m₀⟩ := F.rep _ _ c₀ inferInstance hd
    (SiegelDescent.principal_of_fieldExtension g n _ _ K ℂ ι _ _ c₀ c hc₀ hcp)
  exact ⟨y₀, F.inj ℂ _ _ _ c (by rw [Category.assoc, hy₀, hβ]) (SiegelPullComp.pb_comp m₀ hc₀) hc⟩

end GlobalTheory.SiegDescend

end
