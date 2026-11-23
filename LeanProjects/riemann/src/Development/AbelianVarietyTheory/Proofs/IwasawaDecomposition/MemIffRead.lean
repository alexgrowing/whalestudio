import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianStepLevelOfChartFormsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedTopLevelChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepBeforeClNonempty
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TypeRead

section Read

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {u : B.Word} {j : ℕ} {Ch : Type} {chOf : (I.stp u I.mu0 j).Cl → Ch}
  {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N j) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N j))} {chi : ∀ β, U β →* ℂˣ}
  {y : (I.stp u I.mu0 j).Cl → GA B (B.R.N j)} {st : ∀ c, (I.stp u I.mu0 j).Stab c → GL (Fin (B.R.N j)) B.host.E}
  {k : Ch → GA B (B.R.N j)}

set_option maxHeartbeats 2000000 in

theorem mem_iff_read (H : I.Reads u I.mu0 j chOf Lb U chi y st k) (c : (I.stp u I.mu0 j).Cl) (x : GA B (B.R.N j))
    (hx : x ∈ UAd B.sp.cm (B.R.N j)) :
    x ∈ U (chOf c) ↔ ∃ (hJ : x ∈ J0 B.sp.cm (B.R.N j) ((B.primes X).vT u))
      (hm : (redG B.sp.cm (B.R.N j) ((B.primes X).vT u) (B.primes X).vGs ⟨x, hJ⟩)⁻¹ ∈
        (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) j c.1).grp),
      cosetIn ((I.stp u I.mu0 j).act c.1 (1, ⟨_, hm⟩, 1) ((I.stp u I.mu0 j).rep c)) = cosetIn ((I.stp u I.mu0 j).rep c) := by
  constructor
  · intro hxU
    obtain ⟨q, hq⟩ := OneLevel.pt_exists I.twistPrimes_reference_tuple_eq_empty (OneLevel.reads_base H (chOf c)) (OneLevel.reads_pt H c) hx
    obtain ⟨κ, h1, h2, h3⟩ := (H.lev c x q hq).1 hxU
    subst h2
    obtain ⟨γ, h, θ⟩ := κ
    obtain rfl : γ = 1 := Subtype.ext ((toGLm B.fields.E (B.R.N j)).injective (h1.trans (map_one _).symm))
    obtain ⟨hJ, hr⟩ := OneLevel.pt_read I.twistPrimes_reference_tuple_eq_empty (OneLevel.reads_base H (chOf c)) (OneLevel.reads_pt H c) h.1 θ.1 hq
    obtain rfl : θ = 1 := Subtype.ext (funext fun P => (Finset.eq_empty_iff_forall_notMem.1 I.twistPrimes_reference_tuple_eq_empty P.1 P.2).elim)
    refine ⟨hJ, hr ▸ h.2, ?_⟩
    have e : (⟨_, hr ▸ h.2⟩ : (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) j c.1).grp) = h := Subtype.ext hr
    rw [e]
    exact h3
  · rintro ⟨hJ, hm, hc⟩
    exact OneLevel.mem_of_read H c x hJ hm hc

end Read

end GlobalTheory.Mem.Col2.TypeRead

namespace GlobalTheory.Mem.Col2.TypeRead

section Put

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E))

theorem put_mem_J0 (v : HeightOneSpectrum (𝓞 F)) (hT : v ∉ plUnder F ST) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hx : x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) : rll_put n v x ∈ J0 hc n ST := by
  have hxU : x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := hx.1
  have hxS : x ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n)) := by
    rw [← rll_locL_base n ST v hT]; exact hx.2
  have hS := rll_put_mem_St n v hxS
  refine (mem_mirabolicLevel_iff_reduction hc n ST).2 ⟨rll_put_mem_UAd hc n v hxU, hS, fun P hP => ?_⟩
  rw [rll_put_red n v x hS P (fun h => hT ⟨P, hP, h⟩)]
  exact Subgroup.one_mem _

theorem red_put_off (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hJ : rll_put n v x ∈ J0 hc n ST)
    (w : SG) (hw : ¬ IsOver v w.1) : redG hc n ST SG ⟨rll_put n v x, hJ⟩ w = 1 :=
  rll_put_red n v x (congruence_subgroup_le_stabilizer hc n ST hJ) w.1 hw

theorem red_put_at {gp : Fin 2 → ℕ} (G : GLoc F E hc.sig gp) (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal)
    (w : SG) (e : (𝓞 E ⧸ w.1.asIdeal) ≃+* kv F v)
    (hcomp : ∀ z : Formalism.L2.Herm.intAf F E, ∃ hz : G.phi a v h (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w.1 z))
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hJ : rll_put n v x ∈ J0 hc n ST) :
    ((redG hc n ST SG ⟨rll_put n v x, hJ⟩ w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).map e =
      redM F v (G.mat a v h 1 x) := by
  have hcomp' : ∀ (z : Formalism.L2.Herm.intAf F E), ∃ hz : gloPhi v (G.sp a v h) (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w.1 z) := hcomp
  have hw := GlobalTheory.Mem.LevStd.gloRho_zero_of_compat v (G.sp a v h) (G.sp_alg a v h) w.1 e hcomp'
  have hgE := GlobalTheory.Mem.LevStd.gloE_eq_of_compat v (G.sp a v h) (G.sp_alg a v h) w.1 e hcomp'
  have h1 := gco_red_map n v (G.sp a v h) (G.sp_alg a v h) w.1 hw (congruence_subgroup_le_stabilizer hc n ST hJ)
  have hG : G.mat a v h 1 x = ((bc (gloPhi v (G.sp a v h)) (bc (prV (E := E) v) (rll_put n v x)) : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    rw [rll_put_self]; simp only [GLoc.mat, inv_one, one_mul, mul_one]; rfl
  rw [hG, ← h1]
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, hgE]
  rfl

end Put

end GlobalTheory.Mem.Col2.TypeRead

namespace GlobalTheory.Mem.Col2.TypeRead

section Coset

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

def cvec (p : PtAt R sel mu cst u j) (P : rowSG Pr sel mu) : Fin (R.N j) → 𝓞 X.E ⧸ P.1.asIdeal :=
  redV P.1 ((qOf P.1 : X.E) • Classical.epsilon fun z => z ∈ cosetIn p P)

end Coset

end GlobalTheory.Mem.Col2.TypeRead

namespace GlobalTheory.Mem.Col2.TypeRead

section Fix

variable {K L : Type} [CommRing K] [CommRing L] {n : ℕ}

theorem fix_inv_iff (M : GL (Fin n) K) (c : Fin n → K) :
    ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c = c ↔ (M : Matrix (Fin n) (Fin n) K) *ᵥ c = c := by
  constructor
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem fix_map_iff (e : K ≃+* L) (M : Matrix (Fin n) (Fin n) K) (c : Fin n → K) :
    M.map e *ᵥ (fun i => e (c i)) = (fun i => e (c i)) ↔ M *ᵥ c = c := by
  have h : M.map e *ᵥ (fun i => e (c i)) = fun i => e ((M *ᵥ c) i) := by
    have := RingHom.map_mulVec (e : K →+* L) M c
    funext i
    exact (this i).symm
  rw [h]
  constructor
  · intro h'
    funext i
    exact e.injective (congrFun h' i)
  · intro h'
    rw [h']

end Fix

end GlobalTheory.Mem.Col2.TypeRead

end
