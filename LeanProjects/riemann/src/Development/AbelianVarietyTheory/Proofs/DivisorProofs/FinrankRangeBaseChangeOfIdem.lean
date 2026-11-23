import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAppEqBialgHomKernelIdealOfIdempotents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerIdealFinrankEqPowOfIdempotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocommOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorClosedImmersion
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct Coalgebra Bialgebra GlobalTheory.PDiv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDivGroup.IdemSplit

theorem finrank_range_baseChange_of_idem {R S M : Type} [CommRing R] [CommRing S] [Algebra R S]
    [StrongRankCondition R] [StrongRankCondition S] [AddCommGroup M] [Module R M]
    (e : M →ₗ[R] M) (he : e ∘ₗ e = e) [Module.Free R (LinearMap.range e)] :
    Module.finrank S (LinearMap.range (e.baseChange S)) =
      Module.finrank R (LinearMap.range e) := by
  let r : M →ₗ[R] LinearMap.range e := e.rangeRestrict
  let i : LinearMap.range e →ₗ[R] M := (LinearMap.range e).subtype
  have hri : r ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨y, hy⟩ := x.2
    change e x.1 = x.1
    rw [← hy]
    exact LinearMap.congr_fun he y
  have hir : e = i ∘ₗ r := LinearMap.ext fun _ => rfl
  have hS : r.baseChange S ∘ₗ i.baseChange S = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hri, LinearMap.baseChange_id]
  have hsurj : Function.Surjective (r.baseChange S) := fun x =>
    ⟨i.baseChange S x, LinearMap.congr_fun hS x⟩
  have hinj : Function.Injective (i.baseChange S) := fun x y hxy => by
    have := congrArg (r.baseChange S) hxy
    rwa [← LinearMap.comp_apply, hS, ← LinearMap.comp_apply, hS] at this
  have h2 : e.baseChange S = i.baseChange S ∘ₗ r.baseChange S := by
    rw [← LinearMap.baseChange_comp, ← hir]
  rw [h2, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 hsurj),
    LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]

def quotEquivRange {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (f : A →ₐ[R] A)
    (I : Ideal A) (h : RingHom.ker f = I) : (A ⧸ I) ≃ₗ[R] LinearMap.range f.toLinearMap :=
  (Submodule.Quotient.restrictScalarsEquiv R I).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (by ext x; simp [← h]) ≪≫ₗ
    LinearMap.quotKerEquivRange f.toLinearMap

end GlobalTheory.PDivGroup.IdemSplit

namespace GlobalTheory.PDivGroup.IdemSplit

open GlobalTheory.PDivGroup.KerGrp

theorem exists_of_family {p : ℕ} {k : Type} [CommRing k] (G : PDivGroup p k)
    (v : G ⟶ G) (h₀ : ℕ) (B : ℕ → Type) [∀ n, CommRing (B n)] [∀ n, HopfAlgebra k (B n)]
    [∀ n, Module.Projective k (B n)]
    (π : ∀ n, G.A n →ₐc[k] B n) (hπ : ∀ n, Function.Surjective (π n))
    (hk : ∀ n, RingHom.ker (π n) = kerIdeal (v.app n))
    (h : ∀ (n : ℕ) (q : PrimeSpectrum k), Module.rankAtStalk (B n) q = p ^ (n * h₀)) :
    ∃ (K : PDivGroup p k) (i : K ⟶ G), ∀ n : ℕ, Function.Surjective (i.app n) ∧
      RingHom.ker (i.app n) = kerIdeal (v.app n) := by
  haveI : ∀ n, IsCocomm k (B n) := fun n => isCocomm_of_surjective (π n) (hπ n)
  have hle : ∀ n, RingHom.ker (π (n + 1)) ≤ RingHom.ker ((π n).comp (G.res n)) := fun n a ha => by
    have : G.res n a ∈ RingHom.ker (π n) := by
      rw [hk, ← map_res_kerIdeal]
      rw [hk] at ha
      exact Ideal.mem_map_of_mem (G.res n : G.A (n + 1) →ₐ[k] G.A n) ha
    exact this
  let r := fun n => liftSurj (π (n + 1)) (hπ (n + 1)) ((π n).comp (G.res n)) (hle n)
  have hr : ∀ n a, r n (π (n + 1) a) = π n (G.res n a) := fun n a => liftSurj_apply ..
  let K : PDivGroup p k :=
    { height := h₀
      A := B
      finite := fun n => Module.Finite.of_surjective (π n : G.A n →ₗ[k] B n) (hπ n)
      rank_eq := h
      res := r
      res_surjective := fun n b => by
        obtain ⟨c, rfl⟩ := hπ n b
        obtain ⟨a, rfl⟩ := G.res_surjective n c
        exact ⟨_, hr n a⟩
      ker_res := fun n => by
        rw [← map_torsionIdeal (hπ (n + 1)), ← G.ker_res]
        refine le_antisymm (fun b hb => ?_) (Ideal.map_le_iff_le_comap.2 fun a ha => ?_)
        · obtain ⟨a, rfl⟩ := hπ _ b
          have h1 : G.res n a ∈ RingHom.ker (π n) := (hr n a).symm.trans hb
          rw [hk, ← map_res_kerIdeal] at h1
          obtain ⟨c, hc, e⟩ := (Ideal.mem_map_iff_of_surjective
            (G.res n : G.A (n + 1) →ₐ[k] G.A n) (G.res_surjective n)).1 h1
          rw [← hk] at hc
          have hc' : π (n + 1) c = 0 := hc
          have e' : G.res n c = G.res n a := e
          have h2 : a - c ∈ RingHom.ker (G.res n) := by
            rw [RingHom.mem_ker, map_sub, e', sub_self]
          have h3 : π (n + 1) a = π (n + 1) (a - c) := by rw [map_sub, hc', sub_zero]
          rw [h3]
          exact Ideal.mem_map_of_mem (π (n + 1) : G.A (n + 1) →ₐ[k] B (n + 1)) h2
        · have ha' : G.res n a = 0 := ha
          change r n (π (n + 1) a) = 0
          rw [hr, ha', map_zero] }
  exact ⟨K, ⟨π, fun n => BialgHom.ext fun a => hr n a⟩, fun n => ⟨hπ n, hk n⟩⟩

end GlobalTheory.PDivGroup.IdemSplit

namespace GlobalTheory.PDivGroup.IdemSplit

theorem baseChangeMap_zero {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (O' : Type) [CommRing O']
    [Algebra O O'] (G H : PDivGroup p O) : baseChangeMap O' (0 : G ⟶ H) = 0 := by
  have h := baseChangeMap_add O' (0 : G ⟶ H) 0
  rw [add_zero] at h
  exact (add_eq_left.1 h.symm)

theorem bcMap_toLinearMap {O : Type} [CommRing O] (O' : Type) [CommRing O'] [Algebra O O']
    {A : Type} [CommRing A] [Bialgebra O A] (f : A →ₐc[O] A) :
    ((bcMap O' f : O' ⊗[O] A →ₐ[O'] O' ⊗[O] A)).toLinearMap =
      ((f : A →ₐ[O] A).toLinearMap).baseChange O' := by
  refine LinearMap.ext fun x => ?_
  induction x with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul r a => exact bcMap_tmul f r a

variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O]

theorem idempotent_split_of_isLocalRing (G : PDivGroup p O) (u : G ⟶ G) (hu : u ≫ u = u) :
    ∃ (H : PDivGroup p O) (i : H ⟶ G) (q : G ⟶ H), i ≫ q = 𝟙 H ∧ q ≫ i = u := by
  set v : G ⟶ G := 𝟙 G - u with hv
  have huv : u + v = 𝟙 G := add_sub_cancel u (𝟙 G)
  have h1 : u ≫ v = 0 := by rw [hv, Preadditive.comp_sub, hu, Category.comp_id, sub_self]
  have h2 : v ≫ u = 0 := by rw [hv, Preadditive.sub_comp, hu, Category.id_comp, sub_self]
  have hker : ∀ n, RingHom.ker (u.app n) = kerIdeal (v.app n) :=
    ker_app_eq_kerIdeal_of_idempotents p O G u v huv h1 h2

  let k := IsLocalRing.ResidueField O
  let uk := baseChangeMap k u
  let vk := baseChangeMap k v
  have hF : ∀ {X Y Z : PDivGroup p O} (f : X ⟶ Y) (g : Y ⟶ Z),
      baseChangeMap k (f ≫ g) = baseChangeMap k f ≫ baseChangeMap k g := fun f g =>
    (baseChangeFunctor p O k).map_comp f g
  have hI : baseChangeMap k (𝟙 G) = 𝟙 (G.baseChange k) := (baseChangeFunctor p O k).map_id G
  have hvuk : vk + uk = 𝟙 _ := by rw [← baseChangeMap_add, add_comm, huv, hI]
  have huvk : uk + vk = 𝟙 _ := by rw [add_comm]; exact hvuk
  have h1k : uk ≫ vk = 0 := by rw [← hF, h1, baseChangeMap_zero]
  have h2k : vk ≫ uk = 0 := by rw [← hF, h2, baseChangeMap_zero]
  obtain ⟨h₀, hrk⟩ := kerIdeal_finrank_eq_pow_of_idempotent p k (G.baseChange k) vk uk
    hvuk h2k h1k
  have hkerk : ∀ n, RingHom.ker (uk.app n) = kerIdeal (vk.app n) :=
    ker_app_eq_kerIdeal_of_idempotents p k (G.baseChange k) uk vk huvk h1k h2k

  let e : ∀ n, G.A n →ₗ[O] G.A n := fun n => ((u.app n : G.A n →ₐ[O] G.A n)).toLinearMap
  have he : ∀ n, e n ∘ₗ e n = e n := fun n => LinearMap.ext fun a =>
    DFunLike.congr_fun (congrArg (fun w : G ⟶ G => w.app n) hu) a
  have hproj : ∀ n, Module.Projective O (LinearMap.range (e n)) := fun n =>
    Module.Projective.of_split (LinearMap.range (e n)).subtype (e n).rangeRestrict
      (LinearMap.ext fun x => Subtype.ext (by
        obtain ⟨y, hy⟩ := x.2
        change e n x.1 = x.1
        rw [← hy]
        exact LinearMap.congr_fun (he n) y))
  have hfin : ∀ n, Module.Finite O (LinearMap.range (e n)) := fun n =>
    Module.Finite.of_surjective (e n).rangeRestrict (LinearMap.surjective_rangeRestrict _)
  have hfree : ∀ n, Module.Free O (LinearMap.range (e n)) := fun n =>
    Module.free_of_flat_of_isLocalRing
  let B := fun n => G.A n ⧸ kerIdeal (v.app n)
  have hHopf : ∀ n, (kerIdeal (v.app n)).IsHopfIdeal O := fun n =>
    GlobalTheory.PDiv.isHopfIdeal_kerIdeal_of_bialgHom O _ _ (v.app n)
  let eqv : ∀ n, B n ≃ₗ[O] LinearMap.range (e n) := fun n =>
    quotEquivRange (u.app n : G.A n →ₐ[O] G.A n) _ (hker n)
  have hBproj : ∀ n, Module.Projective O (B n) := fun n =>
    Module.Projective.of_equiv (eqv n).symm
  have hrank : ∀ n, Module.finrank O (B n) = p ^ (n * h₀) := fun n => by
    rw [(eqv n).finrank_eq, ← finrank_range_baseChange_of_idem (S := k) (e n) (he n),
      ← bcMap_toLinearMap, ← (quotEquivRange _ _ (hkerk n)).finrank_eq]
    exact hrk n
  have hBrank : ∀ (n : ℕ) (q : PrimeSpectrum O), Module.rankAtStalk (B n) q = p ^ (n * h₀) :=
    fun n q => by
      haveI := Module.Free.of_equiv (eqv n).symm
      rw [Module.rankAtStalk_eq_finrank_of_free, hrank]
      rfl
  obtain ⟨K, i, hi⟩ := exists_of_family G v h₀ B
    (fun _ => Bialgebra.Quotient.mkBialgHom _) (fun _ => Ideal.Quotient.mk_surjective)
    (fun _ => Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem) hBrank
  obtain ⟨hfac, hcan⟩ := factor_closedImmersion p O K G i (fun n => (hi n).1)
  obtain ⟨q, hq⟩ := hfac G u (fun n => by rw [(hi n).2, hker n])
  have hiv : i ≫ v = 0 := by
    refine hom_ext fun n => BialgHom.ext fun b => ?_
    have h := (kerIdeal_le_ker_iff (v.app n) (i.app n : G.A n →ₐ[O] K.A n)).1 (hi n).2.ge b
    change i.app n (v.app n b) = (1 : WithConv (G.A n →ₐc[O] K.A n)).ofConv b
    refine Eq.trans h ?_
    simp
  have hiu : i ≫ u = i := by
    have e := Preadditive.comp_add _ _ _ i u v
    rw [huv, hiv, add_zero, Category.comp_id] at e
    exact e.symm
  refine ⟨K, i, q, ?_, hq⟩
  apply hcan K
  rw [Category.assoc, hq, hiu, Category.id_comp]

end GlobalTheory.PDivGroup.IdemSplit

theorem GlobalTheory.PDivGroup.IdemSplit.idempotent_split_integers :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
      (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
      [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O →
      ∀ (G : PDivGroup p O) (u : G ⟶ G), u ≫ u = u →
        ∃ (H : PDivGroup p O) (i : H ⟶ G) (q : G ⟶ H), i ≫ q = 𝟙 H ∧ q ≫ i = u :=
  fun p _ _ _ _ _ _ O _ _ _ _ _ _ _ G u hu =>
    GlobalTheory.PDivGroup.IdemSplit.idempotent_split_of_isLocalRing p O G u hu
