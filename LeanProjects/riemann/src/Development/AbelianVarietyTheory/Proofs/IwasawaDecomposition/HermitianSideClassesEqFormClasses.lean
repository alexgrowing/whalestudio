import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.HAt

section GenP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open scoped TensorProduct

theorem val_nat_lt_one (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) (h : (g : 𝓞 F) ∈ v.asIdeal) :
    Valued.v (g : v.adicCompletion F) < 1 := by
  have h1 : v.valuation F (algebraMap (𝓞 F) F (g : 𝓞 F)) < 1 := (v.valuation_lt_one_iff_mem _).2 h
  have h2 : ((g : v.adicCompletion F)) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (g : 𝓞 F)) := by
    simp only [map_natCast]
  rw [h2]
  exact lt_of_eq_of_lt (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 F) F (g : 𝓞 F))) h1

theorem redM_eq_one {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (g : v.adicCompletion F) (hg : Valued.v g < 1)
    (X W : Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hW : ∀ a b, W a b ∈ v.adicCompletionIntegers F)
    (hX : ∀ a b, X a b = (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b + g * W a b) :
    redM F v X = 1 := by
  have hgi : g ∈ v.adicCompletionIntegers F := le_of_lt hg
  have h1 : ∀ a b, (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b ∈ v.adicCompletionIntegers F := by
    intro a b
    by_cases e : a = b
    · subst e
      rw [Matrix.one_apply_eq]
      exact one_mem _
    · rw [Matrix.one_apply_ne e]
      exact zero_mem _
  ext a b
  have hm : X a b ∈ v.adicCompletionIntegers F := by
    rw [hX]
    exact add_mem (h1 a b) (mul_mem hgi (hW a b))
  have hz : IsLocalRing.residue (v.adicCompletionIntegers F) ⟨g, hgi⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := (Valuation.integer.integers (Valued.v (R := v.adicCompletion F))).isUnit_iff_valuation_eq_one.1 hu
    exact absurd this (ne_of_lt hg)
  have e : (⟨X a b, hm⟩ : v.adicCompletionIntegers F) =
      ⟨(1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b, h1 a b⟩ + ⟨g, hgi⟩ * ⟨W a b, hW a b⟩ := by
    exact Subtype.ext ((hX a b).trans rfl)
  simp only [redM]
  rw [dif_pos hm, e, map_add, map_mul, hz, zero_mul, add_zero]
  by_cases ab : a = b
  · subst ab
    simp only [Matrix.one_apply_eq]
    exact map_one _
  · simp only [Matrix.one_apply_ne ab]
    exact map_zero _

theorem mem_Uloc_of_princ {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 F))} {gp : Fin 2 → ℕ} (S : StepLevel F E σ J T f bad) (G : GLoc F E σ gp)
    {H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))}
    {lam : ∀ a v h, H a v h →* ℂˣ} (V : GLevH S G H lam)
    (hLb : ∀ b : Fin n, (Pi.single b 1 : Fin n → E) ∈ S.Lb)
    (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) (hfr : V.fr i v h = 1)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hx : x ∈ levelVL σ J v S.Lb)
    (hc : ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb,
      ∃ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb,
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (gp i : E ⊗[F] v.adicCompletion F) • z) :
    x ∈ S.Uloc v := by
  have hint : ∀ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb, ∀ a,
      G.phi i v h (z a) ∈ v.adicCompletionIntegers F := by
    intro z hz a
    have := (V.fr_lat i v h (fun b => G.phi i v h (z b))).1 ⟨z, hz, fun _ => rfl⟩ a
    rw [hfr] at this
    simpa using this
  have hcol : ∀ b : Fin n, ∃ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb, ∀ a,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b =
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b + (gp i : E ⊗[F] v.adicCompletion F) * z a := by
    intro b
    have e1 : (fun j => inclE (F := F) (v.adicCompletion F) ((Pi.single b 1 : Fin n → E) j)) =
        (Pi.single b 1 : Fin n → E ⊗[F] v.adicCompletion F) := by
      funext j
      by_cases e : j = b
      · subst e
        simp
      · simp [e]
    have hb : (Pi.single b 1 : Fin n → E ⊗[F] v.adicCompletion F) ∈
        latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
      rw [← e1]
      exact Submodule.subset_span ⟨_, hLb b, rfl⟩
    obtain ⟨z, hz, e⟩ := hc _ hb
    refine ⟨z, hz, fun a => ?_⟩
    have := congrFun e a
    rw [Matrix.mulVec_single_one] at this
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at this
    rw [← this]
    by_cases ab : a = b
    · subst ab
      simp
    · simp [ab]
  choose Z hZ hZe using hcol
  refine (V.mem i v h x hx).2 ⟨1, one_mem _, ?_⟩
  have key : redM F v (G.mat i v h (V.fr i v h) x) = 1 := by
    rw [hfr]
    refine redM_eq_one v (gp i : v.adicCompletion F) (val_nat_lt_one v (gp i) h) _
      (fun a b => G.phi i v h (Z b a)) (fun a b => hint _ (hZ b) a) fun a b => ?_
    have e2 : G.mat i v h 1 x a b = G.phi i v h ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b) := by
      simp [GLoc.mat, bc]
    rw [e2, hZe b a, map_add, map_mul, map_natCast]
    congr 1
    by_cases ab : a = b
    · subst ab
      simp
    · simp [ab]
  rw [key]
  rfl

end GenP

section Tr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

open scoped TensorProduct

theorem reGL_rfl_apply {n : ℕ} (R : Type) [CommRing R] (g : GL (Fin n) R) : reGL rfl R g = g := by
  ext a b
  simp [reGL]

theorem reGL_rfl_hom {n : ℕ} (R : Type) [CommRing R] :
    (reGL (rfl : n = n) R).toMonoidHom = MonoidHom.id _ := by
  ext1 g
  exact reGL_rfl_apply R g

theorem reL_rfl {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : reL rfl L = L := by
  ext x
  simp [reL, reV]

theorem co_rfl (S : HSpace E) : co S rfl = Formalism.L2.Herm.crd S :=
  LinearEquiv.ext fun x => funext fun j => by simp [co, Formalism.L2.Herm.crd]

theorem tie_of_forms (hc : CMData F E) (S : HSpace E) {n : ℕ} (h : S.rank = n) (hO : Crd.Ortho S)
    {σ : E →ₐ[F] E} (hσ : σ = hc.sig) {J : Matrix (Fin n) (Fin n) E} (hJ : J = S.gram.reindex (finCongr h) (finCongr h))
    {f : ℕ} {gp : Fin 2 → ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (hbad : bad = {v | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal})
    (St : StepLevel F E σ J 1 f bad) (G : GLoc F E σ gp)
    {H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))}
    {lam : ∀ a v h, H a v h →* ℂˣ} (V : GLevH St G H lam) (hfr : ∀ a v h, V.fr a v h = 1)
    (hLb : ∀ x, x ∈ St.Lb ↔ ∀ j, x j ∈ (algebraMap (𝓞 E) E).range)
    {cls : Type} {stab : cls → Type} [∀ c, Group (stab c)]
    (y : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls St)))
    (lat : cls → Submodule (𝓞 E) (Fin n → E))
    (y_lat : ∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔
      ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) St.Lb)
    (stabI : ∀ c, stab c →* UJ (σ : E →+* E) J)
    (stabI_inj : ∀ c, Function.Injective (stabI c))
    (stabI_range : ∀ c (γ : UJ (σ : E →+* E) J), γ ∈ (stabI c).range ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ St.U.map (MulAut.conj (y c).1).toMonoidHom) :
    ∃ (lattice₂ : cls → Submodule (𝓞 E) S.V) (levP : Formalism.L2.Herm.StepLevel0 hc S gp (Formalism.L2.Herm.crdLat S S.L0))
      (clsP : Formalism.L2.Herm.ClassTie hc S (Formalism.L2.Herm.crdLat S S.L0) levP.U stab lattice₂),
      SameCar h (Formalism.L2.Herm.crdLat S S.L0) St.Lb levP.Uloc St.Uloc levP.U St.U
        (fun c => (clsP.y c).1) (fun c => (y c).1) (fun c s => (clsP.stabI c s).1) (fun c s => (stabI c s).1) ∧
      ∀ c, lat c = (lattice₂ c).map (((co S h : S.V ≃ₗ[E] (Fin n → E)) : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) := by
  subst h
  subst hσ
  obtain rfl : J = S.gram := hJ.trans (by ext a b; simp)
  subst hbad
  have hL : St.Lb = Formalism.L2.Herm.crdLat S S.L0 := by
    ext x
    rw [hLb x, ← hO.mem_standardLattice_iff_integral_coords rfl x]
    unfold Formalism.L2.Herm.crdLat
    rw [show Crd.co S rfl = Formalism.L2.Herm.crd S from co_rfl S]
  have hone : ∀ v : HeightOneSpectrum (𝓞 F), ((1 : ℕ) : 𝓞 F) ∉ v.asIdeal := fun v hv =>
    v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using hv))
  have hs : ∀ b : Fin S.rank, (Pi.single b 1 : Fin S.rank → E) ∈ St.Lb := by
    intro b
    refine (hLb _).2 fun j => ?_
    by_cases e : j = b
    · subst e
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [e]⟩
  refine ⟨fun c => (lat c).map (((Formalism.L2.Herm.crd S).symm : (Fin S.rank → E) →ₗ[E] S.V).restrictScalars (𝓞 E)),
    { Uloc := St.Uloc
      Uloc_lev := fun v => hL ▸ St.Uloc_lev v
      Uloc_hyp := fun v h0 h1 => ?_
      Uloc_g := fun i v hv x hx => ?_
      U := St.U
      U_eq := St.U_eq },
    { y := y
      y_bij := y_bij
      y_lat := fun c x => ?_
      stabI := stabI
      stabI_inj := stabI_inj
      stabI_range := stabI_range }, ⟨?_, fun v => ?_, ?_, fun c => ?_, fun c s => ?_⟩, fun c => ?_⟩
  · rw [St.Uloc_hyp v (by rintro (h | h); exacts [h0 h, h1 h]) (hone v), hL]
  · rw [← hL] at hx
    exact mem_Uloc_of_princ St G V hs i v hv (hfr i v hv) x hx.1 hx.2
  · have e : Formalism.L2.Herm.crdLat S ((lat c).map (((Formalism.L2.Herm.crd S).symm : (Fin S.rank → E) →ₗ[E] S.V).restrictScalars (𝓞 E))) = lat c :=
      Crd.map_symm_map (Formalism.L2.Herm.crd S) (lat c)
    rw [e, ← hL]
    exact y_lat c x
  · rw [reL_rfl, hL]
  · show St.Uloc v = (St.Uloc v).map (reGL rfl _).toMonoidHom
    rw [reGL_rfl_hom, Subgroup.map_id]
  · show St.U = St.U.map (reGL rfl _).toMonoidHom
    rw [reGL_rfl_hom, Subgroup.map_id]
  · exact (reGL_rfl_apply _ _).symm
  · exact (reGL_rfl_apply _ _).symm
  · rw [show co S rfl = Formalism.L2.Herm.crd S from co_rfl S]
    exact (Crd.map_symm_map (Formalism.L2.Herm.crd S) (lat c)).symm

end Tr

set_option maxHeartbeats 4000000 in

theorem clsP_hermitian : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, ∃ (lattice₂ : ((I.rec7 l Z).fm u).clsP → Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).sp.X'.V) (levP : Formalism.L2.Herm.StepLevel0 (I.rec7 l Z).sp.cm (I.rec7 l Z).sp.X' (I.rec7 l Z).host.g (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0)) (clsP : Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm (I.rec7 l Z).sp.X' (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0) levP.U ((I.rec7 l Z).fm u).stabilizer₂ lattice₂), SameCar (rankP (I.rec7 l Z)) (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0) (F u).clsP.lev.Lb levP.Uloc (F u).clsP.lev.Uloc levP.U (F u).clsP.lev.U (fun c => (clsP.y c).1) (fun c => ((F u).clsP.y c).1) (fun c s => (clsP.stabI c s).1) (fun c s => ((F u).clsP.stabI c s).1) ∧ ∀ c, (F u).clsP.lat c = (lattice₂ c).map ((crdP (I.rec7 l Z) : (I.rec7 l Z).sp.X'.V →ₗ[(I.rec7 l Z).host.E] (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) → (I.rec7 l Z).host.E)).restrictScalars (𝓞 (I.rec7 l Z).host.E)) := by
  intro B X I hI hP l Z H F hstd hcar u
  obtain ⟨hs, -, hX', -⟩ := hI.spaces
  have oX' : Crd.Ortho B.sp.X' := by rw [hX']; exact Crd.ortho_pos hs _
  have hr := (hstd u).1.what₂
  have hLb : ∀ x, x ∈ (F u).clsP.lev.Lb ↔ ∀ j, x j ∈ (algebraMap (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E).range := by
    intro x
    refine (hr.lb x).trans ⟨fun hx j => ?_, fun hx j => ?_⟩
    · obtain ⟨r, e, -⟩ := hx j
      exact ⟨r, e.symm⟩
    · obtain ⟨r, e⟩ := hx j
      exact ⟨r, e.symm, fun _ => one_dvd r⟩
  exact tie_of_forms (I.rec7 l Z).sp.cm (I.rec7 l Z).sp.X' (rankP (I.rec7 l Z)) oX' rfl rfl rfl (F u).clsP.lev (F u).gl
    (F u).glevP (hstd u).1.frP hLb (F u).clsP.y (F u).clsP.y_bij (F u).clsP.lat (F u).clsP.y_lat (F u).clsP.stabI
    (F u).clsP.stabI_inj (F u).clsP.stabI_range

end GlobalTheory.Mem.Col2.HAt
