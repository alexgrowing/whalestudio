import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_gen_of_local_on_base {X Y S : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Y ⟶ S) (e : S ⟶ Y) (he : e ≫ p = 𝟙 S)
    (hp : ∀ V : S.Opens, Function.Surjective (pullback.snd p V.ι).appTop.hom)
    (h0 : ∀ (U : Type) [CommGroup U] (h : (S ⟶ X) → U), ∏ k, h (e ≫ φ k) ^ ε k = 1)
    (h : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ t : LB.Gen (LB.LinComb L (fun k => (p ⁻¹ᵁ U).ι ≫ φ k) ε), t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L φ ε), u.IsGen := by
  have loc : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ t : LB.Gen (LB.LinComb L (fun i => (p ⁻¹ᵁ U).ι ≫ φ i) ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (p ⁻¹ᵁ U).toScheme) (b : Z ⟶ S) (z : Z) (J), Good L z J →
        r ≫ (p ⁻¹ᵁ U).ι = b ≫ e → val t r z J = 1 := by
    intro s
    obtain ⟨U, hs, t, ht⟩ := h s
    obtain ⟨n, n₁⟩ : ∃ n : (p ⁻¹ᵁ U).toScheme ⟶ (p ⁻¹ᵁ U).toScheme,
        n ≫ (p ⁻¹ᵁ U).ι = (p ⁻¹ᵁ U).ι ≫ p ≫ e :=
      ⟨IsOpenImmersion.lift (p ⁻¹ᵁ U).ι ((p ⁻¹ᵁ U).ι ≫ p ≫ e) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        have e' := congrArg (fun q => q (p y.1)) he
        exact (congrArg (· ∈ U) e').mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := fun i => (p ⁻¹ᵁ U).ι ≫ φ i) (ε' := ε)
      (fun V _ k => by
        have q := h0 V (fun χ => k ((p ⁻¹ᵁ U).ι ≫ p ≫ χ))
        refine Eq.trans (DVR.prod_sum₂ (K := K) (K' := K) (U := V) _
          (c := ∏ i, k ((p ⁻¹ᵁ U).ι ≫ φ i) ^ ε i) rfl
          (DVR.prod_neg _ _ ((Finset.prod_congr rfl fun i _ => by
            show k (n ≫ _ ≫ _) ^ _ = _
            rw [← Category.assoc n, n₁]; simp only [Category.assoc]).trans q))) ?_
        simp)
      (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t n)))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n)))
    refine ⟨U, hs, t', ht', fun Z r b z J hJ hr => ?_⟩
    have : r ≫ n = r := by
      rw [← cancel_mono (p ⁻¹ᵁ U).ι, Category.assoc, n₁, ← Category.assoc, hr, Category.assoc,
        ← Category.assoc e, he, Category.id_comp]
    rw [hv Z r z J hJ, val_mul hJ, val_inv, val_pull hJ, this, mul_inv_cancel]
  choose U hU t ht hn using loc
  have agree : ∀ (s s' : S) (Z : Scheme.{0}) (r : Z ⟶ (p ⁻¹ᵁ U s).toScheme)
      (r' : Z ⟶ (p ⁻¹ᵁ U s').toScheme) (z : Z) (J), Good L z J →
      r ≫ (p ⁻¹ᵁ U s).ι = r' ≫ (p ⁻¹ᵁ U s').ι → val (t s) r z J = val (t s') r' z J := by
    intro s s' Z r r' z J hJ hr
    let V : S.Opens := U s ⊓ U s'
    have mk : ∀ W : S.Opens, V ≤ W → ∃ m : pullback p V.ι ⟶ (p ⁻¹ᵁ W).toScheme,
        m ≫ (p ⁻¹ᵁ W).ι = pullback.fst p V.ι := fun W hW =>
      ⟨IsOpenImmersion.lift (p ⁻¹ᵁ W).ι (pullback.fst p V.ι) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        have e' := congrArg (fun q => q y) (pullback.condition (f := p) (g := V.ι))
        exact (congrArg (· ∈ W) e').mpr (hW (pullback.snd p V.ι y).2)), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨m, hm⟩ := mk (U s) inf_le_left
    obtain ⟨m', hm'⟩ := mk (U s') inf_le_right
    let e' : V.toScheme ⟶ pullback p V.ι := pullback.lift (V.ι ≫ e) (𝟙 _) (by simp [he])
    have he' : e' ≫ pullback.fst p V.ι = V.ι ≫ e := pullback.lift_fst _ _ _
    obtain ⟨v, hv⟩ : ∃ v : Z ⟶ V.toScheme, v ≫ V.ι = (r ≫ (p ⁻¹ᵁ U s).ι) ≫ p :=
      ⟨IsOpenImmersion.lift V.ι ((r ≫ (p ⁻¹ᵁ U s).ι) ≫ p) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact ⟨(r y).2, (congrArg (fun q => p (q y) ∈ U s') hr).mpr (r' y).2⟩), IsOpenImmersion.lift_fac _ _ _⟩
    let ρ : Z ⟶ pullback p V.ι := pullback.lift (r ≫ (p ⁻¹ᵁ U s).ι) v hv.symm
    have hρ : ρ ≫ pullback.fst p V.ι = r ≫ (p ⁻¹ᵁ U s).ι := pullback.lift_fst _ _ _
    have r₁ : ρ ≫ m = r := by rw [← cancel_mono (p ⁻¹ᵁ U s).ι, Category.assoc, hm, hρ]
    have r₂ : ρ ≫ m' = r' := by rw [← cancel_mono (p ⁻¹ᵁ U s').ι, Category.assoc, hm', hρ, hr]
    have key := gen_unique' hL (φ := fun i => m ≫ (p ⁻¹ᵁ U s).ι ≫ φ i) (ε := ε)
      (φ' := fun i => m' ≫ (p ⁻¹ᵁ U s').ι ≫ φ i) (ε' := ε)
      (fun W _ k => Finset.prod_congr rfl fun i _ => by
        show k (m' ≫ _ ≫ _) ^ _ = k (m ≫ _ ≫ _) ^ _
        rw [← Category.assoc, ← Category.assoc m, hm, hm'])
      (pullback.snd p V.ι) e' (pullback.lift_snd _ _ _) (hp V) (DVR.pullGen_isGen _ _ _ _ (ht s) m)
      (DVR.pullGen_isGen _ _ _ _ (ht s') m') (fun y I hI => by
        rw [val_pull hI, val_pull hI, hn s _ _ V.ι y I hI (by rw [Category.assoc, hm, he']),
          hn s' _ _ V.ι y I hI (by rw [Category.assoc, hm', he'])]) Z ρ z J hJ
    rwa [val_pull hJ, val_pull hJ, r₁, r₂] at key
  obtain ⟨u, hu, -⟩ := glue_gen hL φ ε (fun s => p ⁻¹ᵁ U s) (fun y => ⟨p y, hU _⟩) t ht agree
  exact ⟨u, hu⟩

theorem exists_gen_zsmul {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (k : ℤ) :
    ∃ u : LB.Gen (LB.LinComb L φ (fun i => k * ε i)), u.IsGen := by
  refine ⟨⟨fun j => t.s j ^ k⟩, fun i j => ?_⟩
  have h := congrArg (· ^ k) (ht i j)
  simp only [mul_zpow, ← map_zpow] at h
  refine h.trans (congrArg₂ (· * ·) ?_ rfl)
  refine (Finset.prod_zpow _ _ _).symm.trans (Finset.prod_congr rfl fun a _ => ?_)
  exact (zpow_mul _ _ _).symm.trans (congrArg _ (mul_comm _ _))

theorem exists_gen_neg_of_sym (hG : GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) (hs : Out.Sym A L) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1]), u.IsGen := by
  refine exists_gen_of_local_on_base hL _ _ A.hom η[A].left (Over.w η[A]) (fun V => surj_snd hG hA (Over.mk V.ι))
    (fun U _ h => ?_) (fun s => ?_)
  · have e : η[A].left ≫ (GrpObj.inv : A ⟶ A).left = η[A].left :=
      congrArg (fun q => q.left) (show η[A] ≫ (GrpObj.inv : A ⟶ A) = η[A] from GrpObj.one_inv)
    rw [Fin.prod_univ_two]
    show h (η[A].left ≫ (GrpObj.inv : A ⟶ A).left) ^ (1 : ℤ) * h (η[A].left ≫ 𝟙 _) ^ (-1 : ℤ) = 1
    rw [e, Category.comp_id]; simp
  · obtain ⟨U, hU, t, ht⟩ := hs s
    obtain ⟨t', ht', -⟩ := exists_gen hL
      (φ' := fun k => (A.hom ⁻¹ᵁ U).ι ≫ (![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) k) (ε' := ![1, -1])
      (fun V _ h => by simp [Fin.prod_univ_two]) t ht
    exact ⟨U, hU, t', ht'⟩

theorem exists_gen_negLB : GlobalFnsSt → ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S),
    ∃ nu : LB.Gen (negLB P.A P.L k T), nu.IsGen := by
  intro hG S P k T
  obtain ⟨u, hu⟩ := exists_gen_neg_of_sym hG P.isAb P.isLB P.sym
  obtain ⟨w, hw⟩ := exists_gen_zsmul _ (DVR.pullGen_isGen _ _ _ _ hu (snd T P.A).left) (-k)
  obtain ⟨t, ht, -⟩ := exists_gen P.isLB (K' := Fin 2)
    (φ' := ![(snd T P.A).left, (snd T P.A ≫ (GrpObj.inv : P.A ⟶ P.A)).left]) (ε' := ![k, -k])
    (fun V _ h => by simp [Fin.prod_univ_two, mul_comm]) w hw
  exact ⟨t, ht⟩

end GlobalTheory
