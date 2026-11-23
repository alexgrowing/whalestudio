import Development.EtaleCohomology.EtaleTrace.EtaleTateTwistSectionsDeterminedByPointsOfProper
import Development.EtaleCohomology.TateTwists.StrictHenselianAcyclic
import Development.EtaleCohomology.TateTwists.EtaleSheafSectionsGlueOfForgetIsSheaf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

def PtCov : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} (p : X ⟶ S k), IsProper p →
  ∀ Sv : Sieve X, Sv ∈ Scheme.etaleTopology X → ∃ T : Sieve X, T ∈ Scheme.etaleTopology X ∧
    ∀ (V : Scheme.{0}) (g : V ⟶ X), T.arrows g → ∃ (U : Scheme.{0}) (g' : U ⟶ X) (h : V ⟶ U),
      Sv.arrows g' ∧ h ≫ g' = g ∧ ∃ w : S k ⟶ U, w ≫ g' ≫ p = 𝟙 _

def EtaleTateTwistSectionConstantOnPointsOfConnectedProper : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → ∀ j : ℕ,
  ∀ {X : Scheme.{0}} (p : X ⟶ S k), IsProper p → ∀ s : Sec (tw (l ^ j) 0) X,
    (ConnectedSpace X → ∀ y y' : Pt p, Sec.res y.1 s = Sec.res y'.1 s)

theorem q_nsmul {q : ℕ} {U : Scheme.{0}} (x : Sec (tw q 0) U) : q • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := ULift.ext _ _ (by simp)
  rw [this, zero_smul]

theorem res_comp {q : ℕ} {W V U : Scheme.{0}} (a : W ⟶ V) (b : V ⟶ U) (x : Sec (tw q 0) U) :
    Sec.res (a ≫ b) x = Sec.res a (Sec.res b x) := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem res_nsmul {q : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (x : Sec (tw q 0) U) :
    Sec.res g (c • x) = c • Sec.res g x := map_nsmul _ _ _

theorem res_zero' {q : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec (tw q 0) U) = 0 := map_zero _

theorem primK (k : Type) [Field k] [IsAlgClosed k] (q : ℕ) (hq : (q : k) ≠ 0) : Nonempty (Prim q k) := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q k)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos q k hq0))
  refine ⟨⟨z, isUnit_iff_ne_zero.2 hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hz

theorem etale_tate_twist_zero_section_eq_zero_of_vanishing_at_points (hT : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hC : PtCov) (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k]
    (hl : (l : k) ≠ 0) (j : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : IsProper p) (s : Sec (tw (l ^ j) 0) X)
    (h : ∀ y : Pt p, Sec.res y.1 s = 0) : s = 0 := by
  haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hq : ((l ^ j : ℕ) : k) ≠ 0 := by push_cast; exact pow_ne_zero _ hl
  obtain ⟨ζ0⟩ := primK k (l ^ j) hq
  let φ : k →+* Γ(X, ⊤) := (p.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  obtain ⟨Sv, hSv, hSs⟩ := (hT (l ^ j) 0).1 X (ζ0.map φ) s
  obtain ⟨T, hTm, hTs⟩ := hC k p hp Sv hSv
  refine (EtaleFoundations.etale_sheaf_sections_glue_of_forget_isSheaf (ZMod (l ^ j)) (tw (l ^ j) 0) X).1 s 0 ⟨T, hTm, fun V g hg => ?_⟩
  obtain ⟨U, g', hh, hg', rfl, w, hw⟩ := hTs V g hg
  obtain ⟨c, hc⟩ := hSs U g' hg'
  have h0 : Sec.res g' s = 0 := by
    have e1 : Sec.res w (Sec.res g' s) = 0 := by
      rw [← res_comp]
      exact h ⟨w ≫ g', by rw [Category.assoc]; exact hw⟩
    rw [hc] at e1 ⊢
    rw [res_nsmul, (hT (l ^ j) 0).2.2] at e1
    obtain ⟨m, rfl⟩ := (hT (l ^ j) 0).2.1 (S k) _ c e1
    rw [mul_comm]
    first
      | (rw [mul_nsmul, q_nsmul, nsmul_zero])
      | (rw [mul_nsmul', q_nsmul, nsmul_zero])
      | (rw [mul_nsmul', q_nsmul, smul_zero])
      | (rw [mul_nsmul, q_nsmul, smul_zero])
  rw [res_comp, h0, res_zero', res_zero']

theorem tateTwistSections_determinedByPoints_of_constant (hT : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hC : PtCov) (hK : EtaleTateTwistSectionConstantOnPointsOfConnectedProper) : EtaleTateTwistSectionsDeterminedByPointsOfProper := by
  intro l _ k _ _ hl j X p hp s
  exact ⟨etale_tate_twist_zero_section_eq_zero_of_vanishing_at_points hT hC l k hl j p hp s, hK l k hl j p hp s⟩

end LateralTheory.EtaleTrace
