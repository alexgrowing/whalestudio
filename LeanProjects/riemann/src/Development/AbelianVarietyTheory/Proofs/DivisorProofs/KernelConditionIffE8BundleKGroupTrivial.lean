import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAlongIdIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring
open GlobalTheory.CechPic GlobalTheory.PrincipalIntegral GlobalTheory.KTrivSpread

noncomputable section

namespace GlobalTheory.PrincSubring

section Calc

variable {S : Scheme.{0}} {A : Over S} {n : ℕ}
variable [GrpObj A] [IsCommMonObj A] {π : Pic (A ⊗ A).left}
  (hadd : ∀ (T : Over S) (x x' y : T ⟶ A), pair π (x * x') y = pair π x y + pair π x' y)
  (hsym : ∀ (T : Over S) (x y : T ⟶ A), pair π x y = pair π y x)
variable {G : Over S} [GrpObj G] {pr : Fin n → (G ⟶ A)} (hmon : ∀ u, IsMonHom (pr u))
  (huniv : ∀ (T : Over S) (y : Fin n → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u)
  {W : Matrix (Fin n) (Fin n) ℤ} {L : LB G.left} (hL : L.IsLB) (hLW : cls L hL = quad π W pr)

include hadd hsym hLW hmon huniv in

theorem trivAlong_of_kernelAlong {S' : Scheme.{0}} (g : S' ⟶ S) (hdet : (W + W.transpose).det = 1)
    (hker : ∀ (T : Over S) (a : T.left ⟶ S'), a ≫ g = T.hom → ∀ x : T ⟶ A,
      pair π (snd A T ≫ x) (fst A T) = 0 → x = 1) : TrivAlong G L g := by
  intro T a ha x hx
  have hd : (Out.translDiff G L x).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨z, -, hz⟩ := huniv T fun _ => 1
  refine (hz x fun u₀ => ?_).trans (hz (1 : T ⟶ G) fun u => ?_).symm
  swap
  · have := hmon u
    exact MonObj.one_comp _
  choose V hV c hc using hx
  refine Over.OverMorphism.ext (Scheme.Cover.hom_ext
    (T.left.openCoverOfIsOpenCover V
      (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hV p⟩)) _ _ fun p => ?_)
  let T' : Over S := Over.mk ((V p).ι ≫ T.hom)
  let j : T' ⟶ T := Over.homMk (V p).ι rfl
  have key : ∀ w : Fin n → ℤ, quad π W (fun u => (snd A T' ≫ j) ≫ x ≫ pr u) +
      ∑ u, ((W + W.transpose).mulVec w) u • pair π ((snd A T' ≫ j) ≫ x ≫ pr u) (fst A T') = 0 := fun w => by
    obtain ⟨b, hb, -⟩ := huniv (A ⊗ T') fun v => fst A T' ^ w v
    have h := pull_translDiff hadd hsym hmon hL hLW x (snd A T' ≫ j) b hd
    have k : (lift (snd A T' ≫ j) b).left ≫ (fst T G).left = (snd A T').left ≫ (V p).ι :=
      congrArg (fun q => q.left) (lift_fst (snd A T' ≫ j) b)
    obtain ⟨m, hm⟩ : ∃ m : (A ⊗ T').left ⟶ ((fst T G).left ⁻¹ᵁ V p).toScheme,
        m ≫ ((fst T G).left ⁻¹ᵁ V p).ι = (lift (snd A T' ≫ j) b).left :=
      ⟨IsOpenImmersion.lift _ (lift (snd A T' ≫ j) b).left (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (congrArg (fun q => q y ∈ V p) k).mpr ((snd A T').left y).2), IsOpenImmersion.lift_fac _ _ _⟩
    have h0 := (cls_eq_zero_iff (pull_isLB hd _)).2 ⟨c p, hc p⟩
    rw [cls_pull hd] at h0
    rw [← hm, pull_comp, h0, map_zero] at h
    rw [h]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hb, hsym _ _ (fst A T' ^ w v), pair_zpow hadd, hsym _ (fst A T'), mul_smul]
  have k₀ := key 0
  have k₁ := key ((W + W.transpose).adjugate.mulVec (Pi.single u₀ 1))
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mulVec] at k₁
  simp only [Matrix.mulVec_zero, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at k₀
  rw [k₀, zero_add, Finset.sum_eq_single u₀ (fun v _ hv => by rw [Pi.single_eq_of_ne hv, zero_smul]) (by simp),
    Pi.single_eq_same, one_smul, Category.assoc] at k₁
  have e : j ≫ x ≫ pr u₀ = j ≫ 1 :=
    (hker T' ((V p).ι ≫ a) (by simp [T', ha]) _ k₁).trans (MonObj.comp_one j).symm
  exact congrArg (fun q => q.left) e

include hadd hsym hLW hmon huniv in

theorem kernelAlong_of_trivAlong {S' : Scheme.{0}} (g : S' ⟶ S) (u₀ : Fin n) (hK : TrivAlong G L g)
    (T : Over S) (a : T.left ⟶ S') (ha : a ≫ g = T.hom) (x : T ⟶ A)
    (hx : pair π (snd A T ≫ x) (fst A T) = 0) : x = 1 := by
  obtain ⟨y, hy, -⟩ := huniv T fun u => if u = u₀ then x else 1
  have hz : ∀ (Z : Over S) (b : Z ⟶ T) (z : Z ⟶ A) u, pair π (b ≫ y ≫ pr u) z = 0 := fun Z b z u => by
    rw [hy]
    split_ifs
    · have h := congrArg (pull (lift z b).left) hx
      rwa [pull_pair, map_zero, lift_snd_assoc, lift_fst] at h
    · rw [MonObj.comp_one, pair_one hadd]
  have hd : (Out.translDiff G L y).IsLB := LB.isLB_linComb hL _ _
  have h1 : y = 1 := hK T a ha y fun p => ⟨⊤, trivial, by
    refine (cls_eq_zero_iff (pull_isLB hd _)).1 ?_
    have h := pull_translDiff hadd hsym hmon hL hLW y (fst T G) (snd T G) hd
    simp only [quad, hz, smul_zero, Finset.sum_const_zero, add_zero, lift_fst_snd, Over.id_left] at h
    rw [pull_id] at h
    rw [cls_pull hd]
    exact (congrArg _ h).trans (map_zero _)⟩
  have := hmon u₀
  have h := hy u₀
  rw [if_pos rfl, h1, MonObj.one_comp] at h
  exact h.symm

end Calc

theorem kerAlong_iff_trivAlong : ∀ {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (P : LB (A ⊗ A).left), IsSymmetricPair h A P → Out.RelAmple A (diagPull A P) → ∀ {S' : Scheme.{0}}
    (g : S' ⟶ S), KerAlong A P g ↔ GlobalTheory.KTrivSpread.TrivAlong (Out.powObj A 8) (powLB A P) g := by
  intro S h A _ _ P hs hA S' g
  obtain ⟨hab, -, hP, hr₁, hr₂, hsw⟩ := hs
  have hadd : ∀ (T : Over S) (x x' y : T ⟶ A),
      pair (cls P hP) (x * x') y = pair (cls P hP) x y + pair (cls P hP) x' y := fun T x x' y => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (Biadditive.biadditive_of_triv_axes globalFns_holds S A
      (diagPull A P) hab (pull_isLB hP _) hA P hP hr₁ hr₂ T x x' y).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    unfold PrincipalIntegral.pair
    abel
  have hsym : ∀ (T : Over S) (x y : T ⟶ A), pair (cls P hP) x y = pair (cls P hP) y x := fun T x y => by
    have e : cls P hP = pull (lift (snd A A) (fst A A)).left (cls P hP) :=
      (cls_eq_iff hP (pull_isLB hP _)).2 hsw
    have k : (lift y x).left ≫ (lift (snd A A) (fst A A)).left = (lift x y).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]
    unfold PrincipalIntegral.pair
    rw [← k, pull_comp, ← e]
  obtain ⟨-, hdet⟩ := isE8_W8
  have hmon : ∀ u : Fin 8, IsMonHom (Out.powPr A u) := fun u => inferInstance
  have huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ Out.powObj A 8, ∀ u, x ≫ Out.powPr A u = y u :=
    fun T y => ⟨(Out.powIsLimit A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit A 8).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hL : (powLB A P).IsLB := LB.isLB_linComb hP _ _
  have hLW : cls (powLB A P) hL = quad (cls P hP) GlobalTheory.W8 (Out.powPr A) := cls_linComb hP _ _ _
  have tr : ∀ (T : Over S) (x : T ⟶ A), pair (cls P hP) (snd A T ≫ x) (fst A T) = 0 ↔ IsTrivial (slice A P x) :=
    fun T x => by
      rw [PrincipalIntegral.pair, ← cls_pull hP _ (pull_isLB hP _)]
      exact (cls_eq_zero_iff _).trans (GlobalTheory.SiegelTypings.triv_swap hP x)
  constructor
  · intro hk
    exact trivAlong_of_kernelAlong hadd hsym hmon huniv hL hLW g hdet fun T a ha x hx => hk T a ha x ((tr T x).1 hx)
  · intro hK T a ha x hx
    exact kernelAlong_of_trivAlong hadd hsym hmon huniv hL hLW g 0 hK T a ha x ((tr T x).2 hx)

end GlobalTheory.PrincSubring
