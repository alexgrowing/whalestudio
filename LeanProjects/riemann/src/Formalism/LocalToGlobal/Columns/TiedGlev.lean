import Formalism.LocalToGlobal.Columns.TiedGl

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV
open Formalism.L2.Forms (kv redM InJ)

section Red

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST : Finset (Pl E))
  (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
  (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a))
  (w : Pl E) (hw : ∀ a ∈ w.asIdeal, gloRho v spl halg (oToS F E a) = 0)

theorem gco_exists_red (hT : v ∉ plUnder F ST) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hx : x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) :
    ∃ M : GL (Fin n) (kP w), (M : Matrix (Fin n) (Fin n) (kP w)).map (gloE v spl halg w hw) =
      redM F v ((bc (gloPhi v spl) x : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  have hxS : x ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n)) := by
    rw [← rll_locL_base n ST v hT]; exact hx.2
  have hS := rll_put_mem_St n v hxS
  refine ⟨redAt 1 w ⟨rll_put n v x, hS⟩, ?_⟩
  rw [gco_red_map n v spl halg w hw hS, rll_put_self]

end Red

section Diag

variable {F : Type} [Field F] [NumberField F] (n : ℕ) [NeZero n] (v : HeightOneSpectrum (𝓞 F))

open Classical in

def glvU (c : (v.adicCompletionIntegers F)ˣ) (b : Fin n) : (v.adicCompletionIntegers F)ˣ := if b = lastIdx n then c else 1

def glvD (c : (v.adicCompletionIntegers F)ˣ) : GL (Fin n) (v.adicCompletion F) where
  val := Matrix.diagonal fun b => ((glvU n v c b : v.adicCompletionIntegers F) : v.adicCompletion F)
  inv := Matrix.diagonal fun b => (((glvU n v c b)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext b
    exact congrArg Subtype.val (glvU n v c b).mul_inv
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext b
    exact congrArg Subtype.val (glvU n v c b).inv_mul

theorem glvD_one : glvD n v 1 = 1 := by
  apply Units.ext
  show Matrix.diagonal _ = 1
  rw [← Matrix.diagonal_one]
  congr 1
  funext b
  unfold glvU
  split_ifs <;> rfl

theorem glvU_res {c : (v.adicCompletionIntegers F)ˣ} (hc1 : IsLocalRing.residue (v.adicCompletionIntegers F) c = 1) (b : Fin n) :
    IsLocalRing.residue (v.adicCompletionIntegers F) (glvU n v c b) = 1 := by
  unfold glvU
  split_ifs
  · exact hc1
  · rw [Units.val_one, map_one]

theorem glvU_res_inv {c : (v.adicCompletionIntegers F)ˣ} (hc1 : IsLocalRing.residue (v.adicCompletionIntegers F) c = 1) (b : Fin n) :
    IsLocalRing.residue (v.adicCompletionIntegers F) ((glvU n v c b)⁻¹ : (v.adicCompletionIntegers F)ˣ) = 1 := by
  have h := congrArg (IsLocalRing.residue (v.adicCompletionIntegers F)) (glvU n v c b).inv_mul
  rwa [map_mul, glvU_res n v hc1, mul_one, map_one] at h

theorem glv_red_conj {c : (v.adicCompletionIntegers F)ˣ} (hc1 : IsLocalRing.residue (v.adicCompletionIntegers F) c = 1)
    (A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) (hA : ∀ a b, A a b ∈ v.adicCompletionIntegers F) :
    redM F v ((((glvD n v c)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * A *
      (glvD n v c : Matrix (Fin n) (Fin n) (v.adicCompletion F))) = redM F v A := by
  ext a b
  have e : ((((glvD n v c)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * A *
      (glvD n v c : Matrix (Fin n) (Fin n) (v.adicCompletion F))) a b =
      (((((glvU n v c a)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) * ⟨A a b, hA a b⟩ * (glvU n v c b :
        v.adicCompletionIntegers F) : v.adicCompletionIntegers F) : v.adicCompletion F) := by
    show ((Matrix.diagonal (fun b => ((((glvU n v c b)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) :
      v.adicCompletion F)) * A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
      Matrix.diagonal (fun b => ((glvU n v c b : v.adicCompletionIntegers F) : v.adicCompletion F))) a b = _
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rfl
  have hm : ((((glvD n v c)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * A *
      (glvD n v c : Matrix (Fin n) (Fin n) (v.adicCompletion F))) a b ∈ v.adicCompletionIntegers F := by
    rw [e]; exact Subtype.mem _
  unfold redM
  rw [dif_pos (hA a b), dif_pos hm]
  have e2 : (⟨_, hm⟩ : v.adicCompletionIntegers F) =
      (((glvU n v c a)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) * ⟨A a b, hA a b⟩ * (glvU n v c b :
        v.adicCompletionIntegers F) := Subtype.ext e
  rw [e2, map_mul, map_mul, glvU_res n v hc1, glvU_res_inv n v hc1, one_mul, mul_one]

theorem glv_mulVec_int (c : (v.adicCompletionIntegers F)ˣ) (x : Fin n → v.adicCompletion F) :
    (∀ b, (((glvD n v c)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈
      v.adicCompletionIntegers F) ↔ ∀ b, x b ∈ v.adicCompletionIntegers F := by
  refine forall_congr' fun b => ?_
  have e : (((glvD n v c)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b =
      ((((glvU n v c b)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) * x b := by
    show (Matrix.diagonal (fun b => ((((glvU n v c b)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) :
      v.adicCompletion F))).mulVec x b = _
    rw [Matrix.mulVec_diagonal]
  rw [e]
  constructor
  · intro h
    have h2 := mul_mem (glvU n v c b : v.adicCompletionIntegers F).2 h
    rw [← mul_assoc] at h2
    have h3 : ((glvU n v c b : v.adicCompletionIntegers F) : v.adicCompletion F) *
        ((((glvU n v c b)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 :=
      congrArg Subtype.val (glvU n v c b).mul_inv
    rwa [h3, one_mul] at h2
  · intro h
    exact mul_mem (Subtype.mem _) h

end Diag

section Lev

variable {X : Fields} {Pr : Primes X} {hc : Formalism.BasicNotions.CMData X.F X.E} (hPr : Pr.Ok) (S : GSplit (Pr := Pr) hc) {m : ℕ}
  (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ) (hCh : Ch.Ok)
  {n : ℕ} [NeZero n] {ST : Finset (Pl X.E)} {π : 𝓞 X.E} {T f : ℕ} (Λ : LevFam X.E X.K n Pr.vGs)

theorem glv_chr (h : ↥Λ.grp) : Λ.chr h = ∏ w : Pr.vGs, (Λ w).lam ⟨h.1 w, h.2 w (Set.mem_univ w)⟩ := by
  have h1 : Λ.chr h = (∏ i : Pr.vGs, ((Λ i).lam).comp (piProj (fun w => (Λ w).H) i))
      (show ↥(Subgroup.pi Set.univ fun w : Pr.vGs => (Λ w).H) from h) := rfl
  rw [h1, MonoidHom.finsetProd_apply]
  rfl

theorem glv_mat_red (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal)
    {c : (v.adicCompletionIntegers X.F)ˣ} (hc1 : IsLocalRing.residue (v.adicCompletionIntegers X.F) c = 1)
    (x : GL (Fin n) (X.E ⊗[X.F] v.adicCompletion X.F))
    (hx : ∀ a b, (x : Matrix (Fin n) (Fin n) (X.E ⊗[X.F] v.adicCompletion X.F)) a b ∈ Formalism.BasicNotions.intV X.E v) :
    redM X.F v ((tieGLoc hPr S Ch σ₀ hCh).mat i v h (glvD n v c) x) =
      redM X.F v ((bc (gloPhi v (S.sp i v h)) x : GL (Fin n) (v.adicCompletion X.F)) : Matrix (Fin n) (Fin n) (v.adicCompletion X.F)) :=
  glv_red_conj n v hc1 _ fun a b => gloPhi_int v (S.sp i v h) (S.sp_alg i v h) _ (hx a b)

def glevOf (hB : BasePi ST π) (hTπ : π * cO X.E π = (T : 𝓞 X.E)) (hST : ∀ P : Pl X.E, P ∈ ST ↔ π ∈ P.asIdeal)
    (hcard : ∀ P ∈ ST, Nat.card (𝓞 X.E ⧸ P.asIdeal) = T)
    (hSG : ∀ v : HeightOneSpectrum (𝓞 X.F), (T : 𝓞 X.F) ∈ v.asIdeal → v ∉ plUnder X.F Pr.vGs)
    (hidx : (baseLb X.E n ST).toAddSubgroup.relIndex
      (Submodule.span (𝓞 X.E) (Formalism.BasicNotions.dualSet (hc.sig : X.E →+* X.E) (1 : Matrix (Fin n) (Fin n) X.E) (baseLb X.E n ST))).toAddSubgroup =
        T ^ (2 * f))
    (a t nb skip fc : ℕ) (zl : Bool)
    (c : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g i : 𝓞 X.F) ∈ v.asIdeal → (v.adicCompletionIntegers X.F)ˣ)
    (hc1 : ∀ i v h, IsLocalRing.residue (v.adicCompletionIntegers X.F) (c i v h) = 1)
    (hmem : ∀ i v h (M : GL (Fin n) (kP (gwOf hc hPr i v h).1)), M ∈ (Λ (gwOf hc hPr i v h)).H ↔
      InJ a t fc zl ((M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h)))
    (hlam : ∀ i v h (M : GL (Fin n) (kP (gwOf hc hPr i v h).1)) (hM : M ∈ (Λ (gwOf hc hPr i v h)).H),
      σ₀ (((Λ (gwOf hc hPr i v h)).lam ⟨M, hM⟩ : X.Kˣ) : X.K) =
        Formalism.L2.Forms.lamJ (glmPsi (S.eK hPr i v h) σ₀ (Ch.psi0 (gwOf hc hPr i v h)))
          (fun s => glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) s)) a t nb skip
          ((M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h))) :
    Formalism.L2.Forms.GLev (stepOf hc n (fun w => (Λ w).H) hB hTπ hST hcard hSG hidx ((Units.map σ₀.toMonoidHom).comp Λ.chr))
      (tieGLoc hPr S Ch σ₀ hCh) a t nb skip fc zl where
  fr i v h := glvD n v (c i v h)
  fr_lat i v h x := by
    rw [glv_mulVec_int]
    refine (gco_fr_lat n ST v (S.sp i v h) (S.sp_alg i v h)
      (fun hT => hSG v ((mem_plUnder_iff_norm hc hST T hTπ v).1 hT) ⟨_, (gwOf hc hPr i v h).2, gwOf_over hc hPr i v h⟩) x).trans ?_
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  mem i v h x hx := by
    have hT : v ∉ plUnder X.F ST := fun hT =>
      hSG v ((mem_plUnder_iff_norm hc hST T hTπ v).1 hT) ⟨_, (gwOf hc hPr i v h).2, gwOf_over hc hPr i v h⟩
    have hxS : x ∈ stabGL (Formalism.L2.Herm.locL v (stdLat X.E n)) := by
      rw [← rll_locL_base n ST v hT]; exact hx.2
    rw [rll_locL_std] at hxS
    rw [glv_mat_red hPr S Ch σ₀ hCh i v h (hc1 i v h) x ((afsplit_stab_iff _ x).1 hxS).1]
    refine (gco_mem_levLoc hc n ST Pr.vGs v (S.sp i v h) (S.sp_alg i v h) (fun w => (Λ w).H) (gwOf hc hPr i v h) (S.ker hPr i v h)
      (gwOf_over hc hPr i v h) (fun w' hw' => gwOf_uniq hc hPr i v h w' hw') hT x hx).trans ?_
    constructor
    · rintro ⟨M, hM, e⟩
      rw [← e]
      exact (hmem i v h M).1 hM
    · intro hJ
      obtain ⟨M, e⟩ := gco_exists_red hc n ST v (S.sp i v h) (S.sp_alg i v h) _ (S.ker hPr i v h) hT x hx
      refine ⟨M, (hmem i v h M).2 ?_, e⟩
      have e' : (M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h) = _ := e
      rw [e']
      exact hJ
  chi_eq x := by
    have hJ0 : (x : GL (Fin n) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) ∈ J0 hc n ST := unipotentLevel_le_mirabolicLevel hc n ST Pr.vGs _ x.2
    have hred : ∀ w : Pr.vGs, redAt 1 w.1 ⟨x.1, congruence_subgroup_le_stabilizer hc n ST hJ0⟩ ∈ (Λ w).H := fun w =>
      ((mem_levU hc n ST Pr.vGs _).1 x.2).2 w (Set.mem_univ w)
    have h1 : ((levTyp ((Units.map σ₀.toMonoidHom).comp Λ.chr) x : ℂˣ) : ℂ) =
        ∏ w : Pr.vGs, (σ₀ (((Λ w).lam ⟨redAt 1 w.1 ⟨x.1, congruence_subgroup_le_stabilizer hc n ST hJ0⟩, hred w⟩ : X.Kˣ) : X.K))⁻¹ := by
      show ((((Units.map σ₀.toMonoidHom).comp Λ.chr) (levRed hc n ST Pr.vGs _ x))⁻¹ : ℂˣ).1 = _
      rw [Units.val_inv_eq_inv_val, Finset.prod_inv_distrib]
      congr 1
      show σ₀ ((Λ.chr (levRed hc n ST Pr.vGs _ x) : X.Kˣ) : X.K) = _
      rw [glv_chr, Units.coe_prod, map_prod]
      rfl
    refine h1.trans ?_
    rw [glk_prod hc hPr]
    refine Finset.prod_congr rfl fun i _ => finprod_congr fun v => finprod_congr fun h => ?_
    rw [hlam i v h, glv_mat_red hPr S Ch σ₀ hCh i v h (hc1 i v h) _ (fun a b =>
      afsplit_prV_int v _ (((rll_mem_St_iff n x.1).1 (congruence_subgroup_le_stabilizer hc n ST hJ0)).1 a b))]
    congr 2
    exact gco_red_map n v (S.sp i v h) (S.sp_alg i v h) _ (S.ker hPr i v h) (congruence_subgroup_le_stabilizer hc n ST hJ0)
  chi_unit x := gco_chi_unit hc n ST Pr.vGs _ _ x

end Lev

end Formalism.L2.Col
