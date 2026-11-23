import Mathlib
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.LocalToGlobal.Columns.LevGCount
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Formalism.LocalToGlobal.Columns.DecoFin
import Formalism.LocalToGlobal.Columns.CoefCol
import Formalism.LocalToGlobal.Columns.ColForms
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Glue

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ}

open Classical in

abbrev uSG (SG Q : Finset (HeightOneSpectrum (𝓞 E))) : Finset (HeightOneSpectrum (𝓞 E)) := SG ∪ Q

variable {SG Q : Finset (HeightOneSpectrum (𝓞 E))}

open Classical in

def LevFam.glue (A : LevFam E K n SG) (B : LevFam E K n Q) : LevFam E K n (uSG SG Q) := fun w =>
  if h : w.1 ∈ SG then A ⟨w.1, h⟩ else B ⟨w.1, (Finset.mem_union.mp w.2).resolve_left h⟩

open Classical in
theorem LevFam.glue_of_mem (A : LevFam E K n SG) (B : LevFam E K n Q) (w : uSG SG Q) (h : w.1 ∈ SG) :
    A.glue B w = A ⟨w.1, h⟩ := dif_pos h

open Classical in
theorem LevFam.glue_of_not (A : LevFam E K n SG) (B : LevFam E K n Q) (w : uSG SG Q) (h : w.1 ∉ SG) :
    A.glue B w = B ⟨w.1, (Finset.mem_union.mp w.2).resolve_left h⟩ := dif_neg h

variable (Q) in
open Classical in

def extGLG : GLG E n SG →* GLG E n (uSG SG Q) where
  toFun g w := if h : w.1 ∈ SG then g ⟨w.1, h⟩ else 1
  map_one' := by
    funext w
    by_cases h : w.1 ∈ SG <;> simp [h]
  map_mul' a b := by
    funext w
    by_cases h : w.1 ∈ SG <;> simp [h]

theorem extGLG_of_mem (g : GLG E n SG) (w : uSG SG Q) (h : w.1 ∈ SG) : extGLG Q g w = g ⟨w.1, h⟩ := dif_pos h

theorem extGLG_of_not (g : GLG E n SG) (w : uSG SG Q) (h : w.1 ∉ SG) : extGLG Q g w = 1 := dif_neg h

end Glue

section Norm

def Lev.NormBy {κ K : Type} [CommRing κ] [Field K] {n : ℕ} (l : Lev κ K n) (a : GL (Fin n) κ) : Prop :=
  ∀ h : ↥l.H, ∃ h' : ↥l.H, a⁻¹ * h.1 = h'.1 * a⁻¹ ∧ l.lam h' = l.lam h

theorem Lev.normBy_one {κ K : Type} [CommRing κ] [Field K] {n : ℕ} (l : Lev κ K n) : l.NormBy 1 :=
  fun h => ⟨h, by simp, rfl⟩

theorem Lev.NormBy.inv {κ K : Type} [CommRing κ] [Field K] {n : ℕ} {l : Lev κ K n} {a : GL (Fin n) κ}
    (H : l.NormBy a) : l.inv.NormBy a := fun h => by
  obtain ⟨h', e1, e2⟩ := H h
  exact ⟨h', e1, congrArg (·⁻¹) e2⟩

theorem piChar_apply {K : Type} [Field K] {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)]
    (H : ∀ i, Subgroup (G i)) (lam : ∀ i, ↥(H i) →* Kˣ) (x : ↥(Subgroup.pi Set.univ H)) :
    piChar H lam x = ∏ i, lam i (piProj H i x) := by
  rw [piChar, MonoidHom.finsetProd_apply]
  rfl

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem LevFam.chr_apply (Λ : LevFam X.E X.K n SG) (h : ↥Λ.grp) :
    Λ.chr h = ∏ w, (Λ w).lam ⟨h.1 w, h.2 w (Set.mem_univ w)⟩ :=
  piChar_apply (fun w => (Λ w).H) (fun w => (Λ w).lam) h

theorem LevFam.normBy (Λ : LevFam X.E X.K n SG) (a : GLG X.E n SG) (ha : ∀ w, (Λ w).NormBy (a w)) (h : ↥Λ.grp) :
    ∃ h' : ↥Λ.grp, a⁻¹ * h.1 = h'.1 * a⁻¹ ∧ Λ.chr h' = Λ.chr h := by
  choose f hf1 hf2 using fun w => ha w ⟨h.1 w, h.2 w (Set.mem_univ w)⟩
  refine ⟨⟨fun w => (f w).1, fun w _ => (f w).2⟩, ?_, ?_⟩
  · funext w
    exact hf1 w
  · rw [LevFam.chr_apply, LevFam.chr_apply]
    exact Finset.prod_congr rfl fun w _ => hf2 w

variable (X n ST SG) in

def trF (V : Type) [AddCommGroup V] [Module X.K V] :
    Representation X.K (GLG X.E n SG) (DecoSet X.E n ST SG → V) where
  toFun a :=
    { toFun := fun φ d => φ (((1 : UF X.E n), a⁻¹) • d)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext φ d
    show φ (((1 : UF X.E n), (1 : GLG X.E n SG)⁻¹) • d) = φ d
    rw [inv_one, ← Prod.one_eq_mk, one_smul]
  map_mul' a b := by
    ext φ d
    show φ (((1 : UF X.E n), (a * b)⁻¹) • d) = φ (((1 : UF X.E n), b⁻¹) • ((1 : UF X.E n), a⁻¹) • d)
    rw [smul_smul, Prod.mk_mul_mk, one_mul, mul_inv_rev]

theorem trF_apply (V : Type) [AddCommGroup V] [Module X.K V] (a : GLG X.E n SG) (φ : DecoSet X.E n ST SG → V)
    (d : DecoSet X.E n ST SG) : trF X n ST SG V a φ d = φ (((1 : UF X.E n), a⁻¹) • d) := rfl

theorem trF_mem (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG) (a : GLG X.E n SG)
    (ha : ∀ w, (Λ w).NormBy (a w)) (φ : DecoSet X.E n ST SG → C.V) (hφ : φ ∈ (formGSD C Λ).EqFun) :
    trF X n ST SG C.V a φ ∈ (formGSD C Λ).EqFun := by
  intro g d
  obtain ⟨h', e1, e2⟩ := Λ.normBy a ha g.2
  have h1 : φ ((g.1, (h'.1 : GLG X.E n SG)) • ((1 : UF X.E n), a⁻¹) • (d : DecoSet X.E n ST SG)) =
      ((Λ.chr h' : X.Kˣ) : X.K) • C.rho g.1 (φ (((1 : UF X.E n), a⁻¹) • (d : DecoSet X.E n ST SG))) :=
    hφ ((g.1, h') : FormG Λ) _
  show φ (((1 : UF X.E n), a⁻¹) • (g.1, (g.2.1 : GLG X.E n SG)) • (d : DecoSet X.E n ST SG)) =
    ((Λ.chr g.2 : X.Kˣ) : X.K) • C.rho g.1 (φ (((1 : UF X.E n), a⁻¹) • (d : DecoSet X.E n ST SG)))
  rw [smul_smul, Prod.mk_mul_mk, mul_one] at h1
  rw [smul_smul, Prod.mk_mul_mk, one_mul, e1, h1, e2]

def trRep (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG) {A : Type} [Group A]
    (ι : A →* GLG X.E n SG) (hι : ∀ a w, (Λ w).NormBy (ι a w)) : Representation X.K A (formGSD C Λ).EqFun where
  toFun a := (trF X n ST SG C.V (ι a)).restrict fun φ hφ => trF_mem C Λ (ι a) (hι a) φ hφ
  map_one' := by
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    funext d
    show trF X n ST SG C.V (ι 1) φ.1 d = φ.1 d
    rw [map_one, map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    funext d
    show trF X n ST SG C.V (ι (a * b)) φ.1 d = trF X n ST SG C.V (ι a) (trF X n ST SG C.V (ι b) φ.1) d
    rw [map_mul, map_mul]
    rfl

theorem trRep_apply (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG) {A : Type} [Group A]
    (ι : A →* GLG X.E n SG) (hι : ∀ a w, (Λ w).NormBy (ι a w)) (a : A) (φ : (formGSD C Λ).EqFun)
    (d : DecoSet X.E n ST SG) :
    ((trRep C Λ ι hι a φ : (formGSD C Λ).EqFun) : DecoSet X.E n ST SG → C.V) d =
      (φ : DecoSet X.E n ST SG → C.V) (((1 : UF X.E n), (ι a)⁻¹) • d) := rfl

end Norm

def GSD.repCSD {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok) {A : Type} [Group A]
    (r : Representation K A S.EqFun) : Representation K A (S.toCSD h).Forms where
  toFun a := (S.res h).toLinearMap ∘ₗ r a ∘ₗ (S.res h).symm.toLinearMap
  map_one' := by
    ext1 f
    simp
  map_mul' a b := by
    ext1 f
    simp

section Sel

variable (X : Fields)

def IsSel (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) : Prop :=
  ∀ v, (sel v).asIdeal.under (𝓞 X.F) = v.asIdeal

variable {X}

open Classical in

def QE (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (ξ : Chr X.F X.E X.K) :
    Finset (HeightOneSpectrum (𝓞 X.E)) :=
  if h : (Qprime ξ).Finite then h.toFinset.image sel else ∅

end Sel

theorem rank_X'_eq (R : Ranks) : R.N R.m - 1 = R.r + R.m * R.t := by
  have h1 : R.m * (R.t + 1) = R.m * R.t + R.m := by ring
  have h2 := R.m_add_three_le_k
  unfold Ranks.N Ranks.r
  omega

theorem r_le_X' (R : Ranks) : R.r ≤ R.N R.m - 1 := by
  rw [rank_X'_eq R]
  exact Nat.le_add_right _ _

theorem r_le_nV (R : Ranks) : R.r ≤ R.nV := Nat.le_add_right _ _

section RBlock

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)

def chiAt (w : {w // w ∈ Pr.vGs}) : ℕ → (𝓞 X.E ⧸ w.1.asIdeal)ˣ →* X.Kˣ := extChi fun s => Ch.chi s w

def rP0 : LevFam X.E X.K R.r Pr.vGs := fun w => ⟨HU (𝓞 X.E ⧸ w.1.asIdeal) R.r, psiU (Ch.psi0 w) R.r⟩

def rPsharp : LevFam X.E X.K R.r Pr.vGs := fun w =>
  ⟨HU (𝓞 X.E ⧸ w.1.asIdeal) R.r ⊓ fixCol R.r (𝓞 X.E ⧸ w.1.asIdeal) R.k,
    (psiU (Ch.psi0 w) R.r).comp (Subgroup.inclusion inf_le_left)⟩

def rPsym : LevFam X.E X.K R.r Pr.vGs := fun w =>
  ⟨HPsym (𝓞 X.E ⧸ w.1.asIdeal) R.r R.k R.rS, chiSym (Ch.psi0 w) R.r R.k R.rS⟩

variable (X Pr R) in

def rKg : LevFam X.E X.K R.r Pr.vGs := fun _ => ⟨⊥, 1⟩

end RBlock

section Types

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)

def rowTyG (P : LevFam X.E X.K R.r Pr.vGs) : LevFam X.E X.K (R.N R.m - 1) Pr.vGs := fun w =>
  ⟨HPar (R.N R.m - 1) (𝓞 X.E ⧸ w.1.asIdeal) (r_le_X' R) (List.replicate R.m R.t) (P w).H,
    lamPar (r_le_X' R) (List.replicate R.m R.t) (P w).lam (chiAt Ch w)⟩

def rowTyK : LevFam X.E X.K (R.N R.m - 1) Pr.vGs := fun w =>
  ⟨HKJ (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.r R.t R.m, lamKJ (chiAt Ch w) (R.N R.m - 1) R.r R.t R.m⟩

variable (R) in

def rowTyQ (ξ : Chr X.F X.E X.K) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) : LevFam X.E X.K (R.N R.m - 1) Q := fun P =>
  ⟨HQ (𝓞 X.E ⧸ P.1.asIdeal) (R.N R.m - 1) R.r (R.m * R.t), (lamQP ξ P.1 (R.N R.m - 1) R.r (R.m * R.t))⁻¹⟩

def mtTyG (P : LevFam X.E X.K R.r Pr.vGs) (j : ℕ) : LevFam X.E X.K R.nV Pr.vGs := fun w =>
  ⟨HPar R.nV (𝓞 X.E ⧸ w.1.asIdeal) (r_le_nV R) [R.t] (P w).H,
    (lamPar (r_le_nV R) [R.t] (P w).lam fun _ => chiAt Ch w (j - 1))⁻¹⟩

def mtTyK (j : ℕ) : LevFam X.E X.K R.nV Pr.vGs := fun w =>
  ⟨HKV (𝓞 X.E ⧸ w.1.asIdeal) R.nV R.r R.t, lamKV (chiAt Ch w (j - 1)) R.nV R.r R.t⟩

variable (R) in

def mtTyQ (ξ : Chr X.F X.E X.K) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) : LevFam X.E X.K R.nV Q := fun P =>
  ⟨HQ (𝓞 X.E ⧸ P.1.asIdeal) R.nV R.r R.t, lamQP ξ P.1 R.nV R.r R.t⟩

end Types

section Forms

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

variable (Pr) in

abbrev rowSG : Finset (HeightOneSpectrum (𝓞 X.E)) := uSG Pr.vGs (QE sel (mu : Chr X.F X.E X.K))

def rowTy (P : LevFam X.E X.K R.r Pr.vGs) : LevFam X.E X.K (R.N R.m - 1) (rowSG Pr sel mu) :=
  (rowTyG Ch P).glue (rowTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K)))

def rowTyKK : LevFam X.E X.K (R.N R.m - 1) (rowSG Pr sel mu) :=
  (rowTyK Ch).glue (rowTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K)))

def mtTy (P : LevFam X.E X.K R.r Pr.vGs) (j : ℕ) : LevFam X.E X.K R.nV (rowSG Pr sel mu) :=
  (mtTyG Ch P j).glue (mtTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K)))

def mtTyKK (j : ℕ) : LevFam X.E X.K R.nV (rowSG Pr sel mu) :=
  (mtTyK Ch j).glue (mtTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K)))

@[reducible] def mtildeGSD (P : LevFam X.E X.K R.r Pr.vGs) : GSD X.K :=
  formGSD (rowVal W (rowSG Pr sel mu)) (rowTy Ch sel mu P).inv

@[reducible] def mtildeKGSD : GSD X.K :=
  formGSD (rowVal W (rowSG Pr sel mu)) (rowTyKK Ch sel mu).inv

@[reducible] def mtGSD (P : LevFam X.E X.K R.r Pr.vGs) (j : ℕ) : GSD X.K :=
  formGSD (mtVal W j (rowSG Pr sel mu)) (mtTy Ch sel mu P j).inv

@[reducible] def mtKGSD (j : ℕ) : GSD X.K :=
  formGSD (mtVal W j (rowSG Pr sel mu)) (mtTyKK Ch sel mu j).inv

abbrev MtildeV (P : LevFam X.E X.K R.r Pr.vGs) := (mtildeGSD W Ch sel mu P).EqFun

def MtildeL (P : LevFam X.E X.K R.r Pr.vGs) : Submodule (𝓞 X.K) (mtildeGSD W Ch sel mu P).EqFun :=
  (mtildeGSD W Ch sel mu P).intNab

def MtildeLdel (P : LevFam X.E X.K R.r Pr.vGs) : Submodule (𝓞 X.K) (mtildeGSD W Ch sel mu P).EqFun :=
  (mtildeGSD W Ch sel mu P).intDel

abbrev MtV (P : LevFam X.E X.K R.r Pr.vGs) (j : ℕ) := (mtGSD W Ch sel mu P j).EqFun

def MtL (P : LevFam X.E X.K R.r Pr.vGs) (j : ℕ) : Submodule (𝓞 X.K) (mtGSD W Ch sel mu P j).EqFun :=
  (mtGSD W Ch sel mu P j).intNab

def MtLdel (P : LevFam X.E X.K R.r Pr.vGs) (j : ℕ) : Submodule (𝓞 X.K) (mtGSD W Ch sel mu P j).EqFun :=
  (mtGSD W Ch sel mu P j).intDel

@[reducible] def MtildeCSD (P : LevFam X.E X.K R.r Pr.vGs) (h : (mtildeGSD W Ch sel mu P).Ok) : CSD X.K :=
  (mtildeGSD W Ch sel mu P).toCSD h

@[reducible] def MtildeKCSD (h : (mtildeKGSD W Ch sel mu).Ok) : CSD X.K := (mtildeKGSD W Ch sel mu).toCSD h

@[reducible] def MtCSD (P : LevFam X.E X.K R.r Pr.vGs) (j : ℕ) (h : (mtGSD W Ch sel mu P j).Ok) : CSD X.K :=
  (mtGSD W Ch sel mu P j).toCSD h

@[reducible] def MtKCSD (j : ℕ) (h : (mtKGSD W Ch sel mu j).Ok) : CSD X.K := (mtKGSD W Ch sel mu j).toCSD h

end Forms

section G0

theorem HK_normBy {κ K : Type} [CommRing κ] [Field K] {n r : ℕ} (h : r ≤ n) (bl : List ℕ) (χ : ℕ → κˣ →* Kˣ)
    (g : GL (Fin r) κ) : (⟨HK n κ r bl, lamK χ n r bl⟩ : Lev κ K n).NormBy (diagEmb κ h g) := by
  intro M
  refine ⟨⟨diagEmb κ h g⁻¹ * M.1 * (diagEmb κ h g⁻¹)⁻¹, HK_conj_diagEmb h g⁻¹ M.2⟩, ?_,
    lamK_conj_diagEmb χ h g⁻¹ M⟩
  show (diagEmb κ h g)⁻¹ * M.1 = diagEmb κ h g⁻¹ * M.1 * (diagEmb κ h g⁻¹)⁻¹ * (diagEmb κ h g)⁻¹
  rw [map_inv, inv_inv, mul_assoc, mul_inv_cancel, mul_one]

instance fintype_GLs (E : Type) [Field E] [NumberField E] (SG : Finset (HeightOneSpectrum (𝓞 E))) (n : ℕ) :
    Fintype (GLs E SG n) := Fintype.ofFinite _

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

variable (Pr) in

def unipotentGroupBlockEmbedding {r n : ℕ} (h : r ≤ n) : G0 X.E Pr.vGs r →* GLG X.E n (rowSG Pr sel mu) :=
  (extGLG (QE sel (mu : Chr X.F X.E X.K))).comp (diagonalEmbeddingProduct Pr.vGs h)

theorem rowTyKK_inv_normBy_g0Hat (a : G0 X.E Pr.vGs R.r) (w : rowSG Pr sel mu) :
    ((rowTyKK Ch sel mu).inv w).NormBy (unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) a w) := by
  apply Lev.NormBy.inv
  by_cases h : w.1 ∈ Pr.vGs
  · rw [rowTyKK, LevFam.glue_of_mem _ _ w h]
    show Lev.NormBy _ (extGLG _ (diagonalEmbeddingProduct Pr.vGs (r_le_X' R) a) w)
    rw [extGLG_of_mem _ w h]
    exact HK_normBy (r_le_X' R) _ _ _
  · rw [rowTyKK, LevFam.glue_of_not _ _ w h]
    show Lev.NormBy _ (extGLG _ (diagonalEmbeddingProduct Pr.vGs (r_le_X' R) a) w)
    rw [extGLG_of_not _ w h]
    exact Lev.normBy_one _

theorem mtTyKK_inv_normBy_g0Hat (j : ℕ) (a : G0 X.E Pr.vGs R.r) (w : rowSG Pr sel mu) :
    ((mtTyKK Ch sel mu j).inv w).NormBy (unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) a w) := by
  apply Lev.NormBy.inv
  by_cases h : w.1 ∈ Pr.vGs
  · rw [mtTyKK, LevFam.glue_of_mem _ _ w h]
    show Lev.NormBy _ (extGLG _ (diagonalEmbeddingProduct Pr.vGs (r_le_nV R) a) w)
    rw [extGLG_of_mem _ w h]
    exact HK_normBy (r_le_nV R) _ _ _
  · rw [mtTyKK, LevFam.glue_of_not _ _ w h]
    show Lev.NormBy _ (extGLG _ (diagonalEmbeddingProduct Pr.vGs (r_le_nV R) a) w)
    rw [extGLG_of_not _ w h]
    exact Lev.normBy_one _

def g0HatRepEqFunX : Representation X.K (G0 X.E Pr.vGs R.r) (mtildeKGSD W Ch sel mu).EqFun :=
  trRep _ _ (unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R)) (rowTyKK_inv_normBy_g0Hat Ch sel mu)

def unipotentRightActionFormsV (j : ℕ) : Representation X.K (G0 X.E Pr.vGs R.r) (mtKGSD W Ch sel mu j).EqFun :=
  trRep _ _ (unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R)) (mtTyKK_inv_normBy_g0Hat Ch sel mu j)

def g0Act (h : (mtildeKGSD W Ch sel mu).Ok) :
    Representation X.K (G0 X.E Pr.vGs R.r) (MtildeKCSD W Ch sel mu h).Forms :=
  (mtildeKGSD W Ch sel mu).repCSD h (g0HatRepEqFunX W Ch sel mu)

def unipotentRightActionOnForms (j : ℕ) (h : (mtKGSD W Ch sel mu j).Ok) :
    Representation X.K (G0 X.E Pr.vGs R.r) (MtKCSD W Ch sel mu j h).Forms :=
  (mtKGSD W Ch sel mu j).repCSD h (unipotentRightActionFormsV W Ch sel mu j)

def V0X (Xg : Finset (G0 X.E Pr.vGs R.r → X.K)) (P : LevFam X.E X.K R.r Pr.vGs) :
    Submodule X.K (mtildeKGSD W Ch sel mu).EqFun :=
  LinearMap.range ((g0HatRepEqFunX W Ch sel mu).asAlgebraHom (goodAt Xg P.grp P.chr))

def invariantSubspaceOfForms (j : ℕ) (Xg : Finset (G0 X.E Pr.vGs R.r → X.K)) (P : LevFam X.E X.K R.r Pr.vGs) :
    Submodule X.K (mtKGSD W Ch sel mu j).EqFun :=
  LinearMap.range ((unipotentRightActionFormsV W Ch sel mu j).asAlgebraHom (goodAt Xg P.grp P.chr⁻¹))

end G0

structure InvariantSubspaceData (K : Type) [Field K] [NumberField K] where
  n : ℕ
  d : ℕ
  E : Matrix (Fin n) (Fin d) K
  Pr : Matrix (Fin d) (Fin n) K
  H : Matrix (Fin d) (Fin d) K
  L : Submodule (𝓞 K) (Fin d → K)
  Ldel : Submodule (𝓞 K) (Fin d → K)

def InvariantSubspaceData.of {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G] [Fintype G]
    (r : Representation K G S.Forms) (Xg : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) : InvariantSubspaceData K where
  n := S.dim
  d := S.BaseDimension r Xg P ψ
  E := S.V0E r Xg P ψ
  Pr := S.goodPartProjection r Xg P ψ
  H := S.goodPartHermitianForm r Xg P ψ
  L := S.Mt r Xg P ψ
  Ldel := S.MtDel r Xg P ψ

section V0C

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def V0C (h : (mtildeKGSD W Ch sel mu).Ok) (Xg : Finset (G0 X.E Pr.vGs R.r → X.K))
    (P : LevFam X.E X.K R.r Pr.vGs) : InvariantSubspaceData X.K :=
  InvariantSubspaceData.of (MtildeKCSD W Ch sel mu h) (g0Act W Ch sel mu h) Xg P.grp P.chr

def invariantSubspaceCoordsLevel (j : ℕ) (h : (mtKGSD W Ch sel mu j).Ok) (Xg : Finset (G0 X.E Pr.vGs R.r → X.K))
    (P : LevFam X.E X.K R.r Pr.vGs) : InvariantSubspaceData X.K :=
  InvariantSubspaceData.of (MtKCSD W Ch sel mu j h) (unipotentRightActionOnForms W Ch sel mu j h) Xg P.grp P.chr⁻¹

end V0C

end Formalism.L2.Col
