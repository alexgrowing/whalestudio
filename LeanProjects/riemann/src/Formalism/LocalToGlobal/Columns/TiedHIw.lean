import Formalism.LocalToGlobal.Columns.LocalLevelIsKOneEverywhere
import Formalism.LocalToGlobal.Columns.TiedGlRec

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG
open Formalism.L2.Forms (kv redM InJ aOf fcOf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : CMData F E) (n : ℕ) [NeZero n] (ST : Finset (Pl E))
  (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)

theorem hiw_levelVL_iff (hsig : ∀ x, spl (sigR hc.sig (v.adicCompletion F) x) = swapR _ (spl x))
    (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (hT : v ∉ plUnder F ST)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hx : x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F)) :
    x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ↔
      bc (gloPhi v spl) x ∈ Formalism.UG.GLint (Fin n) (v.adicCompletionIntegers F).toSubring := by
  have hu : ∃ u ∈ Formalism.UG.GLint (Fin n) (v.adicCompletionIntegers F).toSubring,
      (u : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
        fun i j => (spl (inclE (F := F) (v.adicCompletion F) ((1 : Matrix (Fin n) (Fin n) E) i j))).1 := by
    refine ⟨1, one_mem _, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have h1 := Formalism.UG.P.level_subgroup_split F E (Fin n) hc.sig (1 : Matrix (Fin n) (Fin n) E) v spl hsig
    (Formalism.L2.G.split_integral_completion F E v spl halg) hu x hx
  rw [← Formalism.UG.P.level_subgroup_local_standard F E (Fin n) hc.sig (1 : Matrix (Fin n) (Fin n) E) v] at h1
  refine Iff.trans ?_ h1
  have e : latS (F := F) (v.adicCompletion F) (intV E v) (baseLb E n ST) =
      latS (F := F) (v.adicCompletion F) (intV E v) (Formalism.UG.stdLat (n := Fin n) (A := E) (𝓞 E)) := by
    have := rll_locL_base (F := F) n ST v hT
    rw [stdLat_eq_ug] at this
    exact this
  unfold levelVL
  rw [show latS (F := F) (v.adicCompletion F) (tensInt (F := F) (v.adicCompletion F) (intOE E)
    (v.adicCompletionIntegers F).toSubring) (baseLb E n ST) = _ from e]

end Gen

theorem inLevelZero_iff_unitriangular (R : Ranks) {κ : Type} [Field κ] (M : Matrix (Fin (R.N 0)) (Fin (R.N 0)) κ) :
    InJ (aOf R 0) R.t (fcOf R 0) (decide (0 = R.m)) M ↔ ∀ p q : Fin (R.N 0), (q < p → M p q = 0) ∧ M p p = 1 := by
  have hm := R.two_le_m
  have hN : R.N 0 = R.k := by simp [Ranks.N]
  have ha : aOf R 0 = R.k := by unfold aOf; rw [if_pos (by omega)]; rfl
  have hf : fcOf R 0 = R.N 0 := if_neg (by omega)
  have hd : decide (0 = R.m) = false := decide_eq_false (by omega)
  have hb : ∀ x : Fin (R.N 0), Formalism.L2.Forms.blkOf (aOf R 0) R.t x = x := fun x => by
    unfold Formalism.L2.Forms.blkOf; rw [if_pos (by rw [ha, ← hN]; exact x.2)]
  rw [hd, hf]
  constructor
  · rintro ⟨h1, h2, -, -⟩ p q
    exact ⟨fun hqp => h1 p q (by rw [hb, hb]; exact hqp), h2 p (by rw [ha, ← hN]; exact p.2)⟩
  · intro h
    refine ⟨fun x y hxy => (h x y).1 (by rw [hb, hb] at hxy; exact hxy), fun x _ => (h x x).2, ?_, ?_⟩
    · intro x y hy
      exact absurd hy (Nat.ne_of_lt y.2)
    · intro hh
      exact absurd hh (by simp)

section Clo

theorem hiw_closure {κ κ' : Type} [Field κ] [Field κ'] (e : κ ≃+* κ') {n : ℕ} (H : Subgroup (GL (Fin n) κ))
    (hH : ∀ M : GL (Fin n) κ, M ∈ H ↔ ∀ p q : Fin n, (q < p → (M : Matrix (Fin n) (Fin n) κ).map e p q = 0) ∧
      (M : Matrix (Fin n) (Fin n) κ).map e p p = 1)
    (y : GL (Fin n) κ') (hy : y ∈ Subgroup.closure (upperUni n κ')) :
    ∃ M ∈ H, (M : Matrix (Fin n) (Fin n) κ).map e = (y : Matrix (Fin n) (Fin n) κ') := by
  have hle : Subgroup.closure (upperUni n κ') ≤ H.map (bc (e : κ →+* κ')) := by
    rw [Subgroup.closure_le]
    intro z hz
    let M : GL (Fin n) κ := bc (e.symm : κ' →+* κ) z
    have hMz : (M : Matrix (Fin n) (Fin n) κ).map e = (z : Matrix (Fin n) (Fin n) κ') := by
      funext p q
      exact e.apply_symm_apply _
    refine ⟨M, (hH M).2 ?_, Units.ext hMz⟩
    rw [hMz]
    exact hz
  obtain ⟨M, hM, hMy⟩ := hle hy
  exact ⟨M, hM, congrArg Units.val hMy⟩

end Clo

section Col

variable {X : Fields} {Pr : Primes X} {R : Ranks} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (Ch : Chars X Pr R.m)
  (S : GSplit (Pr := Pr) hc) (u : Pr.Word)

theorem hiw_red {F : Type} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (v.adicCompletionIntegers F))
    (p q : Fin n) :
    ((redGL (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) g :
      GL (Fin n) ((v.adicCompletionIntegers F) ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))) :
      Matrix (Fin n) (Fin n) ((v.adicCompletionIntegers F) ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))) p q =
    (redM F v ((bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) g : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)) p q :
      (v.adicCompletionIntegers F) ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) := by
  have hm : ((bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) g : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) p q ∈ v.adicCompletionIntegers F :=
    ((g : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F)) p q).2
  simp only [redM]
  rw [dif_pos hm]
  rfl

include hX hPr in
set_option maxHeartbeats 1000000 in

theorem iwLoc : IwLoc hc u (colLevS Ch 0) S.sp := by
  intro i v h x hxU
  rw [inv_one, one_mul, mul_one]
  have hbad : v ∈ plUnder X.F Pr.vGs :=
    (th_plUnder_vGs hc hPr v).2 (by fin_cases i; exact Or.inl h; exact Or.inr h)
  have hT : v ∉ plUnder X.F (Pr.vT u) := fun hT =>
    rls_T_notUnder hPr u v ((mem_plUnder_iff_norm hc (rls_vT_iff hX hPr u) (Pr.T u) (hPr.piT_norm u) v).1 hT) hbad
  have hlv := hiw_levelVL_iff hc (R.N 0) (Pr.vT u) v (S.sp i v h) (S.sp_sig i v h) (S.sp_alg i v h) hT x hxU
  have hmem : x ∈ levelVL hc.sig (1 : Matrix (Fin (R.N 0)) (Fin (R.N 0)) X.E) v (baseLb X.E (R.N 0) (Pr.vT u)) →
      (x ∈ levLoc hc (R.N 0) (Pr.vT u) Pr.vGs (colLevS Ch 0).grp v ↔
        ∃ M ∈ (colLevS Ch 0 (gwOf hc hPr i v h)).H, (M : Matrix (Fin (R.N 0)) (Fin (R.N 0)) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h) =
          redM X.F v ((bc (gloPhi v (S.sp i v h)) x : GL (Fin (R.N 0)) (v.adicCompletion X.F)) :
            Matrix (Fin (R.N 0)) (Fin (R.N 0)) (v.adicCompletion X.F))) :=
    fun hx => gco_mem_levLoc hc (R.N 0) (Pr.vT u) Pr.vGs v (S.sp i v h) (S.sp_alg i v h)
      (fun w => (colLevS Ch 0 w).H) (gwOf hc hPr i v h) (S.ker hPr i v h) (gwOf_over hc hPr i v h)
      (gwOf_uniq hc hPr i v h) hT x hx
  have hH : ∀ M : GL (Fin (R.N 0)) (kP (gwOf hc hPr i v h).1), M ∈ (colLevS Ch 0 (gwOf hc hPr i v h)).H ↔
      ∀ p q : Fin (R.N 0), (q < p → (M : Matrix (Fin (R.N 0)) (Fin (R.N 0)) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h) p q = 0) ∧
        (M : Matrix (Fin (R.N 0)) (Fin (R.N 0)) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h) p p = 1 :=
    fun M => (colLevS_mem_iff Ch (Nat.zero_le _) _ (S.eK hPr i v h) M).trans (inLevelZero_iff_unitriangular R _)
  constructor
  · intro hx
    have hlev := levLoc_le_levelVL hc (R.N 0) (Pr.vT u) Pr.vGs _ v hx
    obtain ⟨M, hM, hMx⟩ := (hmem hlev).1 hx
    obtain ⟨g, hg⟩ := hlv.1 hlev
    have hI := (hH M).1 hM
    rw [hMx] at hI
    have hgx : ((bc (algebraMap (v.adicCompletionIntegers X.F) (v.adicCompletion X.F)) g : GL (Fin (R.N 0)) (v.adicCompletion X.F)) :
        Matrix (Fin (R.N 0)) (Fin (R.N 0)) (v.adicCompletion X.F)) =
        ((bc (gloPhi v (S.sp i v h)) x : GL (Fin (R.N 0)) (v.adicCompletion X.F)) :
          Matrix (Fin (R.N 0)) (Fin (R.N 0)) (v.adicCompletion X.F)) := congrArg Units.val hg
    refine Subgroup.mem_map.2 ⟨g, ?_, hg⟩
    apply Subgroup.subset_closure
    intro p q
    exact ⟨fun hqp => by rw [hiw_red, hgx]; exact (hI p q).1 hqp, by rw [hiw_red, hgx]; exact (hI p p).2⟩
  · intro hx
    obtain ⟨g, hgU, hg⟩ := Subgroup.mem_map.1 hx
    have hlev : x ∈ levelVL hc.sig (1 : Matrix (Fin (R.N 0)) (Fin (R.N 0)) X.E) v (baseLb X.E (R.N 0) (Pr.vT u)) :=
      hlv.2 ⟨g, hg⟩
    have hgx : ((bc (algebraMap (v.adicCompletionIntegers X.F) (v.adicCompletion X.F)) g : GL (Fin (R.N 0)) (v.adicCompletion X.F)) :
        Matrix (Fin (R.N 0)) (Fin (R.N 0)) (v.adicCompletion X.F)) =
        ((bc (gloPhi v (S.sp i v h)) x : GL (Fin (R.N 0)) (v.adicCompletion X.F)) :
          Matrix (Fin (R.N 0)) (Fin (R.N 0)) (v.adicCompletion X.F)) := congrArg Units.val hg
    refine (hmem hlev).2 ?_
    obtain ⟨M, hM, hMg⟩ := hiw_closure (κ' := kv X.F v) (S.eK hPr i v h) _ hH
      (redGL (IsLocalRing.maximalIdeal (v.adicCompletionIntegers X.F)) g) hgU
    refine ⟨M, hM, hMg.trans ?_⟩
    funext p q
    rw [← hgx]
    exact hiw_red v g p q

end Col

theorem iwAll (d : ColDat) (S : GSplit (Pr := d.Pr) d.sp.cm) : IwAll d S :=
  fun u => by
    rw [d.lev0, ← colLevS_of_lt d.Ch (Nat.lt_of_lt_of_le (by norm_num) d.R.two_le_m)]
    exact iwLoc d.sp.cm d.hX d.hPr d.Ch S u

end Formalism.L2.Col
