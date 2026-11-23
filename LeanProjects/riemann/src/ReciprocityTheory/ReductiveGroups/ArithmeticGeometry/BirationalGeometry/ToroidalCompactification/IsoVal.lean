import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubicalLawRight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A] [IsCommMonObj A'] {L : RigLB A}
  {L' : RigLB A'} (c : CubicalStr A L) (c' : CubicalStr A' L') {f : S' ⟶ S} {Φ : A'.left ⟶ A.left} (hG : GlobalFnsSt)
  (hA : IsAbelianScheme A') (gp : IsGrpPullback A' A f Φ) (w : LB.Iso L'.L (L.L.pull Φ)) (hwg : w.IsGen)
include hG hA hwg

theorem cub_w₀ {T' : Over S'} {z : T'.left} {J J'} (hJ : Good L.L z J) (hJ' : Good L'.L z J') (x x' y : T' ⟶ A') :
    val (L := L.L) (φ := thφ A (x3 A)) (ε := thε) c.t ((lift x (lift x' y)).left ≫ (cubeMapOf gp).F3) z J =
      (∏ I : thK.{0}, gw w ((lift x (lift x' y)).left ≫ thφ A' (x3 A') I) z
        (J (((lift x (lift x' y)).left ≫ thφ A' (x3 A') I) ≫ (cubeMapOf gp).F))
        (J' ((lift x (lift x' y)).left ≫ thφ A' (x3 A') I)) ^ thε I) * cubV c' z J' x x' y := by
  have hPG : PGen w := (isGen_iff w).1 hwg
  obtain ⟨t, ht, htv⟩ := exists_up hPG L.isLB L'.isLB (φ' := thφ A' (x3 A')) (ε := thε) c'.t c'.isGen
  have hpt : ∀ I : thK.{0}, thφ A' (x3 A') I ≫ Φ = (cubeMapOf gp).F3 ≫ thφ A (x3 A) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  have hFF : FormEq (fun I => thφ A' (x3 A') I ≫ Φ) thε
      (fun I => (cubeMapOf gp).F3 ≫ thφ A (x3 A) I) thε := by
    unfold FormEq
    intro U _ h
    simp only [hpt]
  have hu := pullGen_isGen L.L (thφ A (x3 A)) thε c.t c.isGen (cubeMapOf gp).F3
  have he : (lift (1 : A' ⊗ A' ⟶ A') (lift (fst A' A') (snd A' A'))).left ≫ (snd A' (A' ⊗ A')).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd, lift_fst_snd, Over.id_left]
  have hp := surj_snd hG hA (A' ⊗ A')
  have hE : (lift (1 : A' ⊗ A' ⟶ A') (lift (fst A' A') (snd A' A'))).left ≫ (cubeMapOf gp).F3 =
      (lift (1 : Over.mk ((A' ⊗ A').hom ≫ f) ⟶ A)
        (lift (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A')))).left := by
    apply hom_ext_triple
    intro i
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3, cubeMapOf, pushPt] <;>
      exact congrArg (fun q => q.left) (map_one (pushHom gp (A' ⊗ A')))
  have hvt : ∀ (Z0 : Scheme.{0}) (r : Z0 ⟶ (G3 A').left) (z0 : Z0) (J0 : (Z0 ⟶ A.left) → L.L.ι)
      (J0' : (Z0 ⟶ A'.left) → L'.L.ι), Good L.L z0 J0 → Good L'.L z0 J0' →
      val t r z0 J0 = (∏ I : thK.{0}, gw w (r ≫ thφ A' (x3 A') I) z0 (J0 ((r ≫ thφ A' (x3 A') I) ≫ Φ))
        (J0' (r ≫ thφ A' (x3 A') I)) ^ thε I) *
        val (L := L'.L) (φ := thφ A' (x3 A')) (ε := thε) c'.t r z0 J0' := by
    intro Z0 r z0 J0 J0' hJ0 hJ0'
    have hm1 : r z0 ∈ LB.wchart L.L (fun I => thφ A' (x3 A') I ≫ Φ)
        (fun I => J0 (r ≫ (thφ A' (x3 A') I ≫ Φ))) :=
      Set.mem_iInter.2 fun I => hJ0 (r ≫ (thφ A' (x3 A') I ≫ Φ))
    have hm2 : r z0 ∈ LB.wchart L'.L (thφ A' (x3 A')) (fun I => J0' (r ≫ thφ A' (x3 A') I)) :=
      Set.mem_iInter.2 fun I => hJ0' (r ≫ thφ A' (x3 A') I)
    refine (htv Z0 r z0 _ _ hm1 hm2).trans ?_
    simp only [pw, val, Category.assoc] <;> rfl
  have hcov : ∀ q : A'.left, ∃ i, q ∈ L'.L.U i := fun q => by
    have hq : q ∈ (⨆ i, L'.L.U i) := by
      rw [L'.isLB.cover]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hq
  have ac : ∀ {U : Type} [CommGroup U] (a b c d : U), a * b⁻¹ * c⁻¹ * a⁻¹ * d * b * c * d⁻¹ = 1 := by
    intro U _ a b c d
    have e1 : a * b⁻¹ * c⁻¹ * a⁻¹ * d * b * c * d⁻¹ = (a * a⁻¹) * (b⁻¹ * b) * (c⁻¹ * c) * (d * d⁻¹) := by
      ac_rfl
    rw [e1]
    simp
  have key := gen_unique' L.isLB hFF (snd A' (A' ⊗ A')).left
    (lift (1 : A' ⊗ A' ⟶ A') (lift (fst A' A') (snd A' A'))).left he hp hu ht
    (fun q Jq hJq => by
      obtain ⟨J'q, hJ'q⟩ : ∃ J'q : ((A' ⊗ A').left ⟶ A'.left) → L'.L.ι, Good L'.L q J'q :=
        ⟨fun ψ => Classical.choose (hcov (ψ q)), fun ψ => Classical.choose_spec (hcov (ψ q))⟩
      obtain ⟨hh, hhd⟩ : ∃ hh : ((A' ⊗ A').left ⟶ A'.left) → ((A' ⊗ A').left.presheaf.stalk q)ˣ,
          ∀ ψ, hh ψ = gw w ψ q (Jq (ψ ≫ Φ)) (J'q ψ) := ⟨_, fun _ => rfl⟩
      have f1 := (isCub_cubV c (T := Over.mk ((A' ⊗ A').hom ≫ f)) hJq).face
        (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A'))
      have f2 : val (L := L'.L) (φ := thφ A' (x3 A')) (ε := thε) c'.t
          (lift (1 : A' ⊗ A' ⟶ A') (lift (fst A' A') (snd A' A'))).left q J'q = 1 :=
        (isCub_cubV c' (T := A' ⊗ A') hJ'q).face (fst A' A') (snd A' A')
      have f3 := prod_cub (T := A' ⊗ A') (1 : A' ⊗ A' ⟶ A') (fst A' A') (snd A' A') hh
      erw [val_pull]
      rw [hE]
      refine f1.trans ?_
      refine Eq.trans ?_ (hvt _ _ q Jq J'q hJq hJ'q).symm
      rw [f2, _root_.mul_one]
      simp only [← hhd]
      rw [f3]
      simp only [_root_.one_mul]
      exact (ac _ _ _ _).symm
      all_goals exact hJq)
    T'.left (lift x (lift x' y)).left z J hJ
  erw [val_pull] at key
  refine key.trans ((hvt _ _ z J J' hJ hJ').trans ?_)
  rfl
  all_goals exact hJ

omit hG hA hwg [GrpObj A] [GrpObj A'] [IsCommMonObj A] [IsCommMonObj A'] in

def Om {M : LB A.left} {M' : LB A'.left} (w : LB.Iso M' (M.pull Φ)) {Z : Scheme.{0}} {s' : Z ⟶ S'} (z : Z)
    (J : (Z ⟶ A.left) → M.ι) (J' : (Z ⟶ A'.left) → M'.ι) (x : Over.mk s' ⟶ A') : (Z.presheaf.stalk z)ˣ :=
  gw w (show Z ⟶ _ from x.left) z (J (x.left ≫ Φ)) (J' x.left)

omit hG hA hwg in

def cubZ {Z : Scheme.{0}} {s : Z ⟶ S} (z : Z) (J : (Z ⟶ A.left) → L.L.ι) (a b d : Over.mk s ⟶ A) : (Z.presheaf.stalk z)ˣ :=
  cubV c (T := Over.mk s) z J a b d

omit hG hA hwg [GrpObj A] [IsCommMonObj A] in

def valZ {M : LB A.left} {K : Type} [Fintype K] {ε : K → ℤ} {φ : K → ((A ⊗ A).left ⟶ A.left)} (W : LB.Gen (LB.LinComb M φ ε))
    {Z : Scheme.{0}} {s : Z ⟶ S} (z : Z) (J : (Z ⟶ A.left) → M.ι) (a b : Over.mk s ⟶ A) : (Z.presheaf.stalk z)ˣ :=
  val W (show Z ⟶ _ from (lift a b).left) z J

include gp in
theorem cub_w {Z : Scheme.{0}} {s' : Z ⟶ S'} {s : Z ⟶ S} {z : Z} {J J'} (hJ : Good L.L z J) (hJ' : Good L'.L z J')
    (a b d : Over.mk s' ⟶ A') (a₀ b₀ d₀ : Over.mk s ⟶ A) (ha : a.left ≫ Φ = a₀.left) (hb : b.left ≫ Φ = b₀.left)
    (hd : d.left ≫ Φ = d₀.left) : cubZ c z J a₀ b₀ d₀ =
      Om w z J J' (a * b * d) * (Om w z J J' (a * b))⁻¹ * (Om w z J J' (a * d))⁻¹ * (Om w z J J' (b * d))⁻¹ * Om w z J J' a *
        Om w z J J' b * Om w z J J' d * (Om w z J J' (1 : Over.mk s' ⟶ A'))⁻¹ * cubZ c' z J' a b d := by
  have hF3 : (lift a (lift b d)).left ≫ (cubeMapOf gp).F3 = (lift a₀ (lift b₀ d₀)).left := by
    apply hom_ext_triple
    intro i
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3, cubeMapOf]
    · exact ha
    · exact hb
    · exact hd
  have h0 := cub_w₀ (c := c) (c' := c') (hG := hG) (hA := hA) (gp := gp) (w := w) (hwg := hwg)
    (hJ := hJ) (hJ' := hJ') (x := a) (x' := b) (y := d)
  rw [hF3] at h0
  refine h0.trans ?_
  congr 1
  exact prod_cub a b d (fun ψ => gw w ψ z (J (ψ ≫ (cubeMapOf gp).F)) (J' ψ))

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
