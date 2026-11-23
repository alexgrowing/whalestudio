import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheafAlt
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.Generation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
  MvPolynomial

universe w' u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

section Res

variable {X : Scheme.{u}}

private lemma resF_refl (F : X.Modules) {U : X.Opens} (h : U ≤ U) (m : Γ(F, U)) : resF F h m = m := by
  change (F.presheaf.map (homOfLE h).op).hom m = m
  rw [show (homOfLE h).op = 𝟙 (op U) from rfl, F.presheaf.map_id]
  rfl

private lemma resF_injective_of_le (F : X.Modules) {U V : X.Opens} (h : V ≤ U) (h' : U ≤ V) :
    Function.Injective (resF F h) := fun a b hab => by
  have := congrArg (resF F h') hab
  rwa [resF_resF, resF_resF, resF_refl, resF_refl] at this

end Res

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}

private abbrev yR (k j : Fin (n + 1)) : Γ(projectiveSpace A n, stdOpen A n k) :=
  ProjTwist.ratio (grading A n) (X_mem k) (X_mem j)

private def upowS (k : Fin (n + 1)) (m : ℤ) :
    ((preMod (projectiveSpace A n)).obj (twistingSheaf (grading A n) m)).obj (op (stdOpen A n k)) :=
  ProjTwist.upow (grading A n) (X_mem k) m

private lemma upowS_res (k l : Fin (n + 1)) (m : ℕ) :
    resM ((preMod (projectiveSpace A n)).obj (twistingSheaf (grading A n) m))
        (inf_le_right : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n l) (upowS l m) =
      resR (inf_le_left : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n k) (yR (A := A) k l) ^ m •
        resM ((preMod (projectiveSpace A n)).obj (twistingSheaf (grading A n) m))
          (inf_le_left : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n k) (upowS k m) :=
  ProjTwist.upow_res _ _ m

private lemma basicOpen_yR (k j : Fin (n + 1)) :
    (projectiveSpace A n).basicOpen (yR (A := A) k j) = stdOpen A n k ⊓ stdOpen A n j :=
  ProjTwist.basicOpen_ratio _ _

private lemma isAffineOpen_stdOpen_inf (k l : Fin (n + 1)) :
    IsAffineOpen (stdOpen A n k ⊓ stdOpen A n l) := by
  have e : stdOpen A n k ⊓ stdOpen A n l = Proj.basicOpen (grading A n) (X k * X l) :=
    (Proj.basicOpen_mul _ _ _).symm
  rw [e]
  exact Proj.isAffineOpen_basicOpen _ _ (SetLike.mul_mem_graded (X_mem k) (X_mem l)) two_pos

private lemma exists_local (G : (projectiveSpace A n).Modules) [G.IsQuasicoherent] (j : Fin (n + 1))
    (s : Γ(G, stdOpen A n j)) (k : Fin (n + 1)) :
    ∃ (e : ℕ) (g : Γ(G, stdOpen A n k)),
      resF G (inf_le_left : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n k) g =
        resO (inf_le_left : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n k) (yR k j) ^ e •
          resF G (inf_le_right : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n j) s := by
  have hb := basicOpen_yR (A := A) k j
  have hle : (projectiveSpace A n).basicOpen (yR (A := A) k j) ≤ stdOpen A n j :=
    hb.le.trans inf_le_right
  obtain ⟨e, g, hg⟩ := qcoh_exists_res_eq G (isAffineOpen_stdOpen k) (yR k j) (resF G hle s)
  refine ⟨e, g, ?_⟩
  have h2 : stdOpen A n k ⊓ stdOpen A n j ≤ (projectiveSpace A n).basicOpen (yR (A := A) k j) :=
    hb.ge
  have := congrArg (resF G h2) hg
  rw [resF_resF, resF_smul, map_pow, resO_resO, resF_resF] at this
  exact this

private lemma exists_local_uniform (G : (projectiveSpace A n).Modules) [G.IsQuasicoherent]
    (j : Fin (n + 1)) (s : Γ(G, stdOpen A n j)) :
    ∃ (a : ℕ) (g : ∀ k, Γ(G, stdOpen A n k)), ∀ k,
      resF G (inf_le_left : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n k) (g k) =
        resO (inf_le_left : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n k) (yR k j) ^ a •
          resF G (inf_le_right : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n j) s := by
  choose e g hg using exists_local G j s
  refine ⟨Finset.univ.sup e, fun k => yR (A := A) k j ^ (Finset.univ.sup e - e k) • g k, fun k => ?_⟩
  rw [resF_smul, hg, smul_smul, map_pow, ← pow_add,
    Nat.sub_add_cancel (Finset.le_sup (f := e) (Finset.mem_univ k))]

private lemma local_res {G : (projectiveSpace A n).Modules} {j : Fin (n + 1)} {s : Γ(G, stdOpen A n j)}
    {a : ℕ} {g : ∀ k, Γ(G, stdOpen A n k)}
    (hg : ∀ k, resF G (inf_le_left : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n k) (g k) =
        resO (inf_le_left : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n k) (yR k j) ^ a •
          resF G (inf_le_right : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n j) s)
    (k : Fin (n + 1)) {O : (projectiveSpace A n).Opens} (hk : O ≤ stdOpen A n k)
    (hj : O ≤ stdOpen A n j) :
    resF G hk (g k) = resO hk (yR k j) ^ a • resF G hj s := by
  have hO : O ≤ stdOpen A n k ⊓ stdOpen A n j := le_inf hk hj
  have := congrArg (resF G hO) (hg k)
  rw [resF_resF, resF_smul, map_pow, resO_resO, resF_resF] at this
  exact this

private lemma exists_kill (G : (projectiveSpace A n).Modules) [G.IsQuasicoherent] (j : Fin (n + 1))
    (s : Γ(G, stdOpen A n j)) (a : ℕ) (g : ∀ k, Γ(G, stdOpen A n k))
    (hg : ∀ k, resF G (inf_le_left : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n k) (g k) =
        resO (inf_le_left : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n k) (yR k j) ^ a •
          resF G (inf_le_right : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n j) s) :
    ∃ b : ℕ, ∀ k l,
      resO (inf_le_left : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n k) (yR k j) ^ b •
        (resF G (inf_le_left : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n k) (g k) -
          resO (inf_le_left : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n k) (yR k l) ^ a •
            resF G (inf_le_right : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n l) (g l)) = 0 := by
  have key : ∀ k l, ∃ b : ℕ,
      resO (inf_le_left : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n k) (yR k j) ^ b •
        (resF G (inf_le_left : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n k) (g k) -
          resO (inf_le_left : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n k) (yR k l) ^ a •
            resF G (inf_le_right : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n l) (g l)) = 0 := by
    intro k l
    apply qcoh_exists_pow_smul_eq_zero G (isAffineOpen_stdOpen_inf k l)
    set W := stdOpen A n k ⊓ stdOpen A n l
    set f := resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k j)
    have hO : (projectiveSpace A n).basicOpen f = W ⊓ (stdOpen A n k ⊓ stdOpen A n j) := by
      have h1 : (projectiveSpace A n).basicOpen f =
          W ⊓ (projectiveSpace A n).basicOpen (yR (A := A) k j) :=
        Scheme.basicOpen_res _ _ _
      rw [h1, basicOpen_yR]
    have hOW : (projectiveSpace A n).basicOpen f ≤ W := (projectiveSpace A n).basicOpen_le f
    have hOk : (projectiveSpace A n).basicOpen f ≤ stdOpen A n k := hOW.trans inf_le_left
    have hOl : (projectiveSpace A n).basicOpen f ≤ stdOpen A n l := hOW.trans inf_le_right
    have hOj : (projectiveSpace A n).basicOpen f ≤ stdOpen A n j :=
      hO.le.trans (inf_le_right.trans inf_le_right)
    rw [map_sub, resF_resF, resF_smul, resF_resF, map_pow, resO_resO,
      local_res hg k hOk hOj, local_res hg l hOl hOj, smul_smul, sub_eq_zero]
    congr 1
    have hr0 : resO (inf_le_right : W ≤ stdOpen A n l) (yR (A := A) l j) *
        resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k l) =
        resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k j) :=
      ProjTwist.ratio_mul_ratio (𝒜 := grading A n) (X_mem k) (X_mem l) (X_mem j)
    have hr := congrArg (resO hOW) hr0
    rw [map_mul, resO_resO, resO_resO, resO_resO] at hr
    rw [← hr, mul_pow, mul_comm]
  choose b hb using key
  refine ⟨Finset.univ.sup fun p : Fin (n + 1) × Fin (n + 1) => b p.1 p.2, fun k l => ?_⟩
  have hle : b k l ≤ Finset.univ.sup fun p : Fin (n + 1) × Fin (n + 1) => b p.1 p.2 :=
    Finset.le_sup (f := fun p : Fin (n + 1) × Fin (n + 1) => b p.1 p.2) (Finset.mem_univ (k, l))
  rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hb k l, smul_zero]

theorem exists_extend (G : (projectiveSpace A n).Modules) [G.IsQuasicoherent] (j : Fin (n + 1))
    (s : Γ(G, stdOpen A n j)) : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ t : Γ(twist G m, ⊤),
      resF (twist G m) le_top t =
        tensorBasisMap G (twistingSheaf (grading A n) m) (ProjTwist.upow (grading A n) (X_mem j) m)
          le_rfl s := by
  obtain ⟨a, g, hg⟩ := exists_local_uniform G j s
  obtain ⟨b, hb⟩ := exists_kill G j s a g hg
  refine ⟨a + b, fun m hm => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right a b) hm)
  have hdb : b ≤ d := by omega

  let ρ : ∀ k : ULift.{u} (Fin (n + 1)), Γ(twist G (a + d : ℕ), stdOpen A n k.down) := fun k =>
    tensorBasisMap G (twistingSheaf (grading A n) (a + d : ℕ))
      (upowS k.down (a + d : ℕ))
      (le_rfl : stdOpen A n k.down ≤ stdOpen A n k.down) (yR (A := A) k.down j ^ d • g k.down)
  have hcov : ∀ x ∈ (⊤ : (projectiveSpace A n).Opens),
      ∃ k : ULift.{u} (Fin (n + 1)), x ∈ stdOpen A n k.down := by
    intro x _
    have hx : x ∈ ⨆ i, stdOpen A n i := by rw [iSup_stdOpen]; trivial
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hx
    exact ⟨⟨k⟩, hk⟩
  have hcompat : ∀ k l : ULift.{u} (Fin (n + 1)),
      resF (twist G (a + d : ℕ))
          (inf_le_left : stdOpen A n k.down ⊓ stdOpen A n l.down ≤ stdOpen A n k.down) (ρ k) =
        resF (twist G (a + d : ℕ))
          (inf_le_right : stdOpen A n k.down ⊓ stdOpen A n l.down ≤ stdOpen A n l.down) (ρ l) := by
    rintro ⟨k⟩ ⟨l⟩
    simp only [ρ]
    unfold twist
    rw [tensorBasisMap_res, tensorBasisMap_res,
      tensorBasisMap_change (s := upowS k (a + d : ℕ))
        (upowS l (a + d : ℕ)) (inf_le_left.trans le_rfl)
        (inf_le_right.trans le_rfl) _ (upowS_res k l (a + d))]
    congr 1
    set W := stdOpen A n k ⊓ stdOpen A n l
    have hr0 : resO (inf_le_right : W ≤ stdOpen A n l) (yR (A := A) l j) *
        resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k l) =
        resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k j) :=
      ProjTwist.ratio_mul_ratio (𝒜 := grading A n) (X_mem k) (X_mem l) (X_mem j)
    have e1 := hb k l
    have e2 : resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k j) ^ d •
        (resF G (inf_le_left : W ≤ stdOpen A n k) (g k) -
          resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k l) ^ a •
            resF G (inf_le_right : W ≤ stdOpen A n l) (g l)) = 0 := by
      rw [← Nat.sub_add_cancel hdb, pow_add, mul_smul, e1, smul_zero]
    rw [smul_sub, sub_eq_zero] at e2
    change resF G (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k j ^ d • g k) =
      (resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k l) ^ (a + d)) •
        resF G (inf_le_right : W ≤ stdOpen A n l) (yR (A := A) l j ^ d • g l)
    rw [resF_smul, resF_smul, map_pow, map_pow, e2, smul_smul, smul_smul, ← hr0]
    congr 1
    ring
  obtain ⟨t, ht⟩ := sheaf_exists_glue ⟨(twist G (a + d : ℕ)).presheaf, (twist G (a + d : ℕ)).isSheaf⟩
    (V := ⊤) (fun k : ULift.{u} (Fin (n + 1)) => stdOpen A n k.down) (fun _ => le_top) hcov ρ
    hcompat
  refine ⟨t, ?_⟩
  have htj : resF (twist G (a + d : ℕ)) le_top t = ρ ⟨j⟩ := ht ⟨j⟩
  refine htj.trans ?_
  have hjj : yR (A := A) j j = 1 := ProjTwist.ratio_self (X_mem j)
  have hgj : g j = s := by
    apply resF_injective_of_le G (inf_le_left : stdOpen A n j ⊓ stdOpen A n j ≤ stdOpen A n j)
      (le_inf le_rfl le_rfl)
    rw [hg j, hjj, map_one, one_pow, one_smul]
  have hx : yR (A := A) j j ^ d • g j = s := by rw [hjj, one_pow, one_smul, hgj]
  exact congrArg (tensorBasisMap G (twistingSheaf (grading A n) (a + d : ℕ))
    (upowS j (a + d : ℕ)) (le_rfl : stdOpen A n j ≤ stdOpen A n j)) hx

def twistLinear (G : (projectiveSpace A n).Modules) (j : Fin (n + 1)) (q : ℤ) :
    Γ(G, stdOpen A n j) →ₗ[Γ(projectiveSpace A n, stdOpen A n j)] Γ(twist G q, stdOpen A n j) where
  toFun := tensorBasisMap G (twistingSheaf (grading A n) q) (upowS j q)
    (le_rfl : stdOpen A n j ≤ stdOpen A n j)
  map_add' := map_add _
  map_smul' r m := tensorBasisMap_smul _ r m

lemma twistLinear_surjective (G : (projectiveSpace A n).Modules) (j : Fin (n + 1)) (q : ℤ) :
    Function.Surjective (twistLinear G j q) :=
  (tensorBasisMap_bijective (ProjTwist.isBasisOn_upow (grading A n) (X_mem j) q) le_rfl).2

theorem exists_generatingSections_twist (G : (projectiveSpace A n).Modules) (hG : IsCoherent G) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∃ σ : (twist G q).GeneratingSections, σ.IsFiniteType := by
  obtain ⟨hqc, hfin⟩ := hG
  have hfg : ∀ j : Fin (n + 1), ∃ S : Finset Γ(G, stdOpen A n j),
      Submodule.span Γ(projectiveSpace A n, stdOpen A n j) (S : Set Γ(G, stdOpen A n j)) = ⊤ :=
    fun j => (hfin _ (isAffineOpen_stdOpen j)).fg_top
  choose S hS using hfg
  have hext : ∀ p : (j : Fin (n + 1)) × S j, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ t : Γ(twist G m, ⊤), resF (twist G m) (le_top : stdOpen A n p.1 ≤ ⊤) t =
        twistLinear G p.1 m p.2.1 := fun p => exists_extend G p.1 p.2.1
  choose m₀ hm₀ using hext
  refine ⟨Finset.univ.sup m₀, fun q hq => ?_⟩
  have hq' : ∀ p, m₀ p ≤ q := fun p => (Finset.le_sup (f := m₀) (Finset.mem_univ p)).trans hq
  choose t ht using fun p => hm₀ p q (hq' p)
  have hcov : (⨆ i : ULift.{u} (Fin (n + 1)), stdOpen A n i.down) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← iSup_stdOpen (A := A) (n := n)]
    exact iSup_le fun j => le_iSup_of_le (⟨j⟩ : ULift.{u} (Fin (n + 1))) le_rfl
  refine exists_generatingSections (twist G q) (fun i : ULift.{u} (Fin (n + 1)) => stdOpen A n i.down)
    (fun i => isAffineOpen_stdOpen _) hcov t fun ⟨j⟩ => ?_
  rw [eq_top_iff]
  rintro z -
  obtain ⟨w, rfl⟩ := twistLinear_surjective G j q z
  have hw : w ∈ Submodule.span Γ(projectiveSpace A n, stdOpen A n j) (S j : Set Γ(G, stdOpen A n j)) :=
    (hS j).symm ▸ Submodule.mem_top
  have hmap := Submodule.mem_map_of_mem (f := twistLinear G j q) hw
  rw [Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨⟨j, ⟨x, hx⟩⟩, ht ⟨j, ⟨x, hx⟩⟩⟩

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
