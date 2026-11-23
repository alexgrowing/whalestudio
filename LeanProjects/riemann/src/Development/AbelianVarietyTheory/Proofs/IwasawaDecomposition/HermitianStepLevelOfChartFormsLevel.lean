import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeUnramifiedUniformizer
import Formalism.LocalToGlobal.Columns.RecLevelLocT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValNatCastLtOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UlocOfTrivDisc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ULocDualHformOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelActsTriviallyOnDiscriminantGroupStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryScalarEqOneModOfFixesSimpleModuleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDvdOfAdicValuationLtOneStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.Lv

section Build
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem reL_rfl {a : ℕ} (L : Submodule (𝓞 E) (Fin a → E)) : reL (rfl : a = a) L = L := by
  ext x
  simp [reL, reV, LinearEquiv.funCongrLeft, LinearMap.funLeft]

theorem reGL_rfl_map {a : ℕ} {R : Type} [CommRing R] (U : Subgroup (GL (Fin a) R)) :
    U.map (reGL (rfl : a = a) R).toMonoidHom = U := by
  have : ∀ x, reGL (rfl : a = a) R x = x := fun x => by
    ext i j
    simp [reGL]
  ext x
  simp [Subgroup.mem_map, this]

theorem exists_herm_level (hc : CMData F E) (S : HSpace E) {n : ℕ} (h : S.rank = n) (gp : Fin 2 → ℕ) (T f : ℕ)
    {bad : Set (HeightOneSpectrum (𝓞 F))} {J : Matrix (Fin n) (Fin n) E} (hJ : J = S.gram.reindex (finCongr h) (finCongr h))
    (K : StepLevel F E hc.sig J T f bad)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), (gp 0 : 𝓞 F) ∉ v.asIdeal → (gp 1 : 𝓞 F) ∉ v.asIdeal → v ∉ bad)
    (hg : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → ∀ x ∈ levelVL hc.sig J v K.Lb,
      (∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) K.Lb, ∃ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) K.Lb,
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = ((gp a : ℕ) : E ⊗[F] v.adicCompletion F) • z) → x ∈ K.Uloc v)
    (hT : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∀ x, x ∈ K.Uloc v ↔ x ∈ levelVL hc.sig J v K.Lb ∧
      ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J K.Lb)),
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ latS (F := F) (v.adicCompletion F) (intV E v) K.Lb) :
    ∃ L : Formalism.L2.Herm.StepLevel hc S gp T f, K.Lb = reL h L.Lb ∧
      (∀ v, K.Uloc v = (L.Uloc v).map (reGL h _).toMonoidHom) ∧ K.U = L.U.map (reGL h _).toMonoidHom := by
  subst h
  have hJ' : J = S.gram := by rw [hJ]; ext a b; simp
  subst hJ'
  clear hJ
  refine ⟨{ Lb := K.Lb, Lb_fin := K.Lb_fin, Lb_span := K.Lb_span, Lb_int := fun x hx => Submodule.subset_span (K.Lb_int x hx),
            Lb_dual := ?_, Lb_index := K.Lb_index, Uloc := K.Uloc, Uloc_lev := K.Uloc_lev, Uloc_hyp := ?_, Uloc_g := ?_, UlocAlt := ?_,
            U := K.U, U_eq := K.U_eq }, ?_, ?_, ?_⟩
  · intro y hy
    unfold Formalism.L2.Herm.dualL at hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact K.Lb_dual y hy
    | zero => simp
    | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
    | smul s a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ _ ha
  · intro v h0 h1 h2
    exact K.Uloc_hyp v (hbad v h0 h1) h2
  · intro a v h x hx
    exact hg a v h x hx.1 hx.2
  · intro v h x
    exact hT v h x
  · exact (reL_rfl _).symm
  · intro v; exact (reGL_rfl_map _).symm
  · exact (reGL_rfl_map _).symm

end Build
end GlobalTheory.Mem.Col2.Lv

namespace GlobalTheory.Mem.Col2.Lv
section W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem uloc_T_iff (σ : E →ₐ[F] E) (hdeg : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x → x ∈ (algebraMap F E).range)
    (hun : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ θ t : 𝓞 E, (t : E) = σ θ ∧ θ - t ∉ P) {n : ℕ} [NeZero n] {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1)
    {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (p q : 𝓞 E) (hq : (q : E) = σ (p : E))
    (hpq : (p : E) * (q : E) = (T : E)) (hT : T.Prime) (hL : S.Lb = rll_dLat n ((p : E)⁻¹))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (hunif : ∀ a : v.adicCompletionIntegers F, Valued.v (a : v.adicCompletion F) < 1 → ∃ b : v.adicCompletionIntegers F, a = (T : v.adicCompletionIntegers F) * b)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
    x ∈ S.Uloc v ↔ x ∈ levelVL σ J v S.Lb ∧
      ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
  subst hJ
  have hT0 : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT.ne_zero
  have hp0 : (p : E) ≠ 0 := fun h => hT0 (by rw [← hpq, h, zero_mul])
  refine ⟨fun hx => ⟨S.Uloc_lev v hx, GlobalTheory.T.level_acts_trivially_on_discriminant_group σ hσ S p q hq hpq hT.ne_zero hL ?_ v hv ?_ x hx⟩, fun h => GlobalTheory.uloc_of_triv_disc σ S v hv x h.1 h.2⟩
  · rw [hL]; exact GlobalTheory.uLocDual_eq σ hσ n p q hp0 hq
  · intro m hm d c hd hc
    exact GlobalTheory.T.unitaryScalar_eq_one_mod_of_fixes_simple_module σ hdeg hσ hfix hun v T hT hunif (S.fM v hv) (S.fM_card v hv) m hm d c hd hc

end W

theorem baseL_eq (B : Base) (n : ℕ) [NeZero n] (t : 𝓞 B.host.E) (ht : (t : B.host.E) ≠ 0) (L : Submodule (𝓞 B.host.E) (Fin n → B.host.E))
    (h : ∀ x, x ∈ L ↔ x ∈ baseL B n t) : L = rll_dLat n ((t : B.host.E)⁻¹) := by
  have hlast : ∀ j : Fin n, j.1 + 1 = n ↔ j = lastIdx n := by
    intro j
    have := NeZero.pos n
    constructor
    · intro e; apply Fin.ext; simp [lastIdx]; omega
    · intro e; rw [e]; simp [lastIdx]; omega
  ext x
  rw [h, rll_mem_dLat]
  constructor
  · intro hx
    refine ⟨fun i _ => ?_, ?_⟩
    · obtain ⟨r, e, -⟩ := hx i
      exact ⟨r, e.symm⟩
    · obtain ⟨r, e, hd⟩ := hx (lastIdx n)
      obtain ⟨c, rfl⟩ := hd ((hlast _).2 rfl)
      refine ⟨c, ?_⟩
      rw [e]
      show _ = _ * algebraMap (𝓞 B.host.E) B.host.E (t * c)
      rw [map_mul]
      exact (inv_mul_cancel_left₀ ht _).symm
  · rintro ⟨h1, c, hc⟩ j
    by_cases hj : j = lastIdx n
    · subst hj
      refine ⟨t * c, ?_, fun _ => dvd_mul_right _ _⟩
      have e : x (lastIdx n) = (t : B.host.E) * (c : B.host.E) := by
        have : algebraMap (𝓞 B.host.E) B.host.E c = (t : B.host.E)⁻¹ * x (lastIdx n) := hc
        show _ = _
        rw [show (c : B.host.E) = algebraMap (𝓞 B.host.E) B.host.E c from rfl, this, mul_inv_cancel_left₀ ht]
      rw [e]; rfl
    · obtain ⟨r, hr⟩ := h1 j hj
      exact ⟨r, hr.symm, fun e => absurd ((hlast j).1 e) hj⟩

end GlobalTheory.Mem.Col2.Lv

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.Mem.Col2.TC.level_of_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (i : ℕ) (hi : i ≤ (I.rec7 l Z).R.m) {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
  {lat : cl → Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E)}
  (K : LevelChart (I.rec7 l Z) ((I.rec7 l Z).mem u).A.T (badG (I.rec7 l Z)) i hi stab lat)
  {Hs : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g a : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal →
    Subgroup (GL (Fin ((I.rec7 l Z).R.N i)) (kv (I.rec7 l Z).host.F v))} {lam : ∀ a v h, Hs a v h →* ℂˣ},
  GLevH K.lev F.gl Hs lam → (∀ x, x ∈ K.lev.Lb ↔ x ∈ baseL B ((I.rec7 l Z).R.N i) (X.piT u)) →
  ∃ L : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f,
    K.lev.Lb = reL (rankN (I.rec7 l Z) i hi) L.Lb ∧
    (∀ v, K.lev.Uloc v = (L.Uloc v).map (reGL (rankN (I.rec7 l Z) i hi) _).toMonoidHom) ∧
    K.lev.U = L.U.map (reGL (rankN (I.rec7 l Z) i hi) _).toMonoidHom := by
  intro B X I hI hP l Z u Ch chOf F hF i hi cl stab _ lat K Hs lam hG hLb
  have hgram : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  haveI : NeZero ((I.rec7 l Z).R.N i) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  let s : 𝓞 (I.rec7 l Z).host.E →+* 𝓞 (I.rec7 l Z).host.E := RingOfIntegers.mapRingHom (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)
  have hsc : ∀ x, (s x : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj (x : (I.rec7 l Z).host.E) := fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
  have hpq : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) * (s F.atT.piU : (I.rec7 l Z).host.E) = (((I.rec7 l Z).mem u).A.T : (I.rec7 l Z).host.E) := by
    rw [hsc]; exact F.atT.piU_norm
  have hTp := ((I.rec7 l Z).mem u).A.T_prime
  have hp0 : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) ≠ 0 := fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
  have hL : K.lev.Lb = rll_dLat ((I.rec7 l Z).R.N i) (((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E)⁻¹) := by
    refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ F.atT.piU hp0 K.lev.Lb ?_
    rw [hF.piU]; exact hLb
  refine GlobalTheory.Mem.Col2.Lv.exists_herm_level (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (I.rec7 l Z).host.g _ _ rfl K.lev ?_ ?_ ?_
  · intro v h0 h1 hb
    rcases hb with hb | hb
    · exact h0 hb
    · exact h1 hb
  · intro a v h x hx hp
    exact GlobalTheory.Mem.LevCong.mem_Uloc_of_cong _ K.lev F.gl hG a v h x hx hp
  · intro v h x
    exact GlobalTheory.Mem.Col2.Lv.uloc_T_iff (sigD (I.rec7 l Z)) (I.rec7 l Z).sp.cm.deg2 (fun x => star_star x) (fun x hx => ((I.rec7 l Z).sp.cm.fixed x).1 hx)
      (I.rec7 l Z).sp.cm.cmUnram.2.2 hgram K.lev F.atT.piU (s F.atT.piU) rfl hpq hTp hL v h (GlobalTheory.T.levelPrime_dvd_of_adicValuation_lt_one (I.rec7 l Z) u F.atT v h) x

end
