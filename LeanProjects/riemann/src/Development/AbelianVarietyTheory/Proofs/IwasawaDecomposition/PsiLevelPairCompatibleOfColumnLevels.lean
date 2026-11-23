import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Columns.RecLevelSym
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.PsiTie

theorem symPos_eq_symm {r k rS : ℕ} (hr : k + rS ≤ r) (i : Fin r) :
    symPos r rS k i = (Formalism.L2.Col.symPerm r k rS).symm i := by
  apply Fin.ext
  rw [Formalism.L2.Col.symPerm_symm_val hr]
  unfold symPos Formalism.L2.Col.symIdxInv
  have hi := i.2
  show (if i.val < rS then k + i.val else if i.val < rS + k then i.val - rS else i.val) % r = _
  rw [Nat.mod_eq_of_lt (by split_ifs <;> omega)]
  split_ifs <;> omega

theorem symPos_entries_iff {κ : Type} [CommRing κ] {r k rS : ℕ} (hr : k + rS ≤ r) (M y : GL (Fin r) κ) :
    (∀ i j : Fin r, (M : Matrix (Fin r) (Fin r) κ) (symPos r rS k i) (symPos r rS k j) =
      (y : Matrix (Fin r) (Fin r) κ) i j) ↔ Formalism.L2.Col.toSymOrd κ r k rS M = y := by
  simp only [symPos_eq_symm hr]
  constructor
  · intro h
    exact Units.ext (Matrix.ext fun i j => by rw [Formalism.L2.Col.toSymOrd_val]; exact h i j)
  · rintro rfl i j
    rfl

theorem baseLevel_character_preserved_placewiseIdentity {E : Type} [Field E] [NumberField E] {LL : Type} [CommRing LL] {r : ℕ} {S T : Finset (Pl E)}
    (hT : T = S) (e : G0 S r ≃* G0 T r) (he : ∀ g P (h : P ∈ S) (h' : P ∈ T), e g ⟨P, h'⟩ = g ⟨P, h⟩)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) LL) :
    (∀ g, g ∈ (P0 S r ψ).H ↔ e g ∈ (P0 T r ψ).H) ∧
      ∀ (g : (P0 S r ψ).H) (h : e g ∈ (P0 T r ψ).H), (P0 S r ψ).chi g = (P0 T r ψ).chi ⟨e g, h⟩ := by
  subst hT
  have hid : ∀ g, e g = g := fun g => funext fun P => he g P.1 P.2 P.2
  refine ⟨fun g => by rw [hid], fun g h => ?_⟩
  exact congrArg _ (Subtype.ext (hid g).symm)

theorem piChar_apply' {K : Type} [Field K] {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i))
    (lam : ∀ i, ↥(H i) →* Kˣ) (x : ↥(Subgroup.pi Set.univ H)) :
    Formalism.L2.Col.piChar H lam x = ∏ i, lam i (Formalism.L2.Col.piProj H i x) :=
  MonoidHom.finset_prod_apply _ _ _

theorem ofLocal_chi_apply {E : Type} [Field E] [NumberField E] {LL : Type} [CommRing LL] {r : ℕ} {Pg : Finset (Pl E)}
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) (cl : ∀ PP : ↥Pg, Hl PP →* LLˣ) (x : ↥(Subgroup.pi Set.univ Hl)) :
    (LevelP.ofLocal Hl cl).chi x = ∏ PP, cl PP (LevelP.prj Hl PP x) :=
  MonoidHom.finset_prod_apply _ _ _

theorem sym_tie {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m)
    {T : Finset (Pl X.E)} (hT : T = Pr.vGs) (e : Formalism.L2.Col.G0 X.E Pr.vGs R.r ≃* G0 T R.r)
    (he : ∀ g P (h : P ∈ Pr.vGs) (h' : P ∈ T), e g ⟨P, h'⟩ = g ⟨P, h⟩)
    (ψ : ∀ PP : Pl X.E, AddChar (kP PP) X.K) (hψ : ∀ P (h : P ∈ Pr.vGs), ψ P = Ch.psi0 ⟨P, h⟩) :
    (∀ g, g ∈ (Formalism.L2.Col.rPsymF Ch).grp ↔ ∃ y ∈ (PsharpSym T R.r R.rS R.k ψ).H, ∀ (PP : ↥T) (i j : Fin R.r),
      ((e g PP : GL (Fin R.r) (kP PP.1)) : Matrix (Fin R.r) (Fin R.r) (kP PP.1)) (symPos R.r R.rS R.k i) (symPos R.r R.rS R.k j) =
        ((y PP : GL (Fin R.r) (kP PP.1)) : Matrix (Fin R.r) (Fin R.r) (kP PP.1)) i j) ∧
    ∀ (g : (Formalism.L2.Col.rPsymF Ch).grp) (y : (PsharpSym T R.r R.rS R.k ψ).H), (∀ (PP : ↥T) (i j : Fin R.r),
      ((e g PP : GL (Fin R.r) (kP PP.1)) : Matrix (Fin R.r) (Fin R.r) (kP PP.1)) (symPos R.r R.rS R.k i) (symPos R.r R.rS R.k j) =
        (((y : G0 T R.r) PP : GL (Fin R.r) (kP PP.1)) : Matrix (Fin R.r) (Fin R.r) (kP PP.1)) i j) →
      (Formalism.L2.Col.rPsymF Ch).chr g = (PsharpSym T R.r R.rS R.k ψ).chi y := by
  subst hT
  have hid : ∀ g, e g = g := fun g => funext fun P => he g P.1 P.2 P.2
  have hr : R.k + R.rS ≤ R.r := by have := Formalism.L2.Col.r_eq_sym R; omega
  refine ⟨fun g => ?_, fun g y hgy => ?_⟩
  · rw [hid]
    constructor
    · intro hg
      refine ⟨fun PP => Formalism.L2.Col.toSymOrd _ R.r R.k R.rS (g PP), (Subgroup.mem_pi _).2 fun PP _ => ?_,
        fun PP => (symPos_entries_iff hr _ _).2 rfl⟩
      have := (Subgroup.mem_pi _).1 hg PP (Set.mem_univ _)
      change g PP ∈ Formalism.L2.Col.HPsymF _ R.r R.k R.rS at this
      rw [Formalism.L2.Col.HPsymF_eq_comap_unipSym, Subgroup.mem_comap] at this
      exact this
    · rintro ⟨y, hy, hyg⟩
      refine (Subgroup.mem_pi _).2 fun PP _ => ?_
      change g PP ∈ Formalism.L2.Col.HPsymF _ R.r R.k R.rS
      rw [Formalism.L2.Col.HPsymF_eq_comap_unipSym, Subgroup.mem_comap, (symPos_entries_iff hr _ _).1 (hyg PP)]
      exact (Subgroup.mem_pi _).1 hy PP (Set.mem_univ _)
  · rw [hid] at hgy
    have h1 := piChar_apply' (fun w => (Formalism.L2.Col.rPsymF Ch w).H) (fun w => (Formalism.L2.Col.rPsymF Ch w).lam) g
    have h2 := ofLocal_chi_apply (fun PP : ↥Pr.vGs => unipSym (kP PP.1) R.r R.rS R.k)
      (fun PP => addCharHom (ψ PP.1) (symHom (kP PP.1) R.r R.rS R.k)) y
    refine h1.trans (Eq.trans ?_ h2.symm)
    refine Finset.prod_congr rfl fun w _ => ?_
    have hy : (y : G0 Pr.vGs R.r) w = Formalism.L2.Col.toSymOrd _ R.r R.k R.rS ((g : Formalism.L2.Col.G0 X.E Pr.vGs R.r) w) :=
      ((symPos_entries_iff hr _ _).1 (hgy w)).symm
    have hM : Formalism.L2.Col.toSymOrd _ R.r R.k R.rS ((g : Formalism.L2.Col.G0 X.E Pr.vGs R.r) w) ∈ unipSym (kP w.1) R.r R.rS R.k := by
      rw [← hy]; exact (Subgroup.mem_pi _).1 y.2 w (Set.mem_univ _)
    apply Units.ext
    have e1 := Formalism.L2.Col.chiSym_eq_symHom (Ch.psi0 w) R.r R.k R.rS
      ⟨_, Formalism.L2.Col.mem_HPsymF.1 ((Subgroup.mem_pi _).1 g.2 w (Set.mem_univ _))⟩ hM
    refine e1.trans ?_
    rw [hψ w.1 w.2]
    congr 2
    exact Subtype.ext hy.symm

theorem psiPPTie_of_levOf : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (cG : G0 L.Pg X.toD7.R.r ≃* G0g X.toD7.nd) (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ L.Pg) (iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1), I.Ok → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → (∀ kv, ((plg kv : L.Pg) : Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) → (∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv)) → PsiPPTie X.toD7 (lev0 I) (chr0 I) (lev1 I) (chr1 I) (eG.trans cG) := by
  intro X px I U L eG cG plg iso hOk hLev hId hpl hbc
  have hψ : ∀ P (h : P ∈ (X.B.primes px).vGs), psiC I P = I.Ch.psi0 ⟨P, h⟩ := fun P h => psiC_of_mem I h
  have hP0 := baseLevel_character_preserved_placewiseIdentity (S := (X.B.primes px).vGs) hLev.Pg eG (fun g P h h' => hId g P h h') (psiC I)
  have hS := sym_tie I.Ch hLev.Pg eG (fun g P h h' => hId g P h h') (psiC I) hψ
  refine ⟨L.Pg, plg, fun kv => (iso kv).symm, psiC I, eG, ?_, ?_⟩
  · refine ⟨hpl, ?_, ?_, hP0.1, hP0.2, hS.1, hS.2⟩
    · intro g kv
      rw [hbc g kv]
      apply Units.ext
      ext i j
      simp [Matrix.GeneralLinearGroup.map, Formalism.UG.bc]
    · intro PP hPP
      rw [hLev.Pg] at hPP
      rw [psiC_of_mem I hPP]
      exact hOk.ch_ok.psi_zero_nontrivial_character _
  · intro kv c b hb
    have hw : ((plg kv : L.Pg) : Pl X.toD7.host.E) ∈ (X.B.primes px).vGs := hLev.Pg ▸ (plg kv).2
    have h := hOk.weil ⟨_, hw⟩ c b hb
    rw [psiC_of_mem I hw]
    refine h.trans ?_
    have hq : Formalism.L2.Col.qOf ((⟨_, hw⟩ : {w // w ∈ (X.B.primes px).vGs}) : Pl X.B.fields.E) = X.toD7.host.g kv.1 :=
      absNorm_eq_of_res X.toD7 (iso kv).symm
    rw [hq]

end GlobalTheory.Mem.PsiTie
