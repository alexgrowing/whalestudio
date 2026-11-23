import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CompLocOfApart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.InvPol

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

def OHat (p : ℕ) (E : Type) [Field E] [NumberField E] : AddSubgroup (AfP p ⊗[ℚ] E) :=
  AddSubgroup.closure {z | ∃ (a : AfP p) (x : 𝓞 E), IsIntAf a ∧ z = a ⊗ₜ (x : E)}

structure AdQ (p : ℕ) where
  ρ : AfQ →+* AfP p
  surj : Function.Surjective ρ
  ker : ∀ a, ρ a = 0 ↔ ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∉ v.asIdeal → a v = 0
  int : ∀ a, IsIntAf (ρ a) ↔ ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∉ v.asIdeal → Valued.v (a v) ≤ 1

structure AdT (p : ℕ) (E : Type) [Field E] [NumberField E] [IsCMField E] extends AdQ p where
  Φ : Af E →+* AfP p ⊗[ℚ] E
  Φ_E : ∀ x : E, Φ (algebraMap E (Af E) x) = 1 ⊗ₜ x
  Φ_Q : ∀ a : AfQ, Φ (finiteAdeleMap ℚ E a) = ρ a ⊗ₜ 1
  Φ_surj : Function.Surjective Φ
  Φ_ker : ∀ x, Φ x = 0 ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → pLoc E w x = 0
  Φ_int : ∀ x, Φ x ∈ OHat p E ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → Valued.v (pLoc E w x) ≤ 1
  Φ_conj : ∀ x, Φ (conjFin (conjE E) x) = conjT E (AfP p) (Φ x)

def AdQEx : Prop := ∀ (p : ℕ) [Fact p.Prime], Nonempty (AdQ p)

def AdTensor : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ ι : AfQ ⊗[ℚ] E ≃+* Af E,
  (∀ (a : AfQ) (x : E), ι (a ⊗ₜ x) = finiteAdeleMap ℚ E a * algebraMap E (Af E) x) ∧
  (∀ y, y ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E), (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)} ↔
    ∀ w : Plc E, Valued.v (pLoc E w (ι y)) ≤ 1) ∧
  ∀ a : AfQ, conjFin (conjE E) (finiteAdeleMap ℚ E a) = finiteAdeleMap ℚ E a

def IdemP : Prop := ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [NumberField E], ∃ e : AfQ,
  (∀ v : Plc ℚ, ((p : 𝓞 ℚ) ∈ v.asIdeal → e v = 1) ∧ ((p : 𝓞 ℚ) ∉ v.asIdeal → e v = 0)) ∧
  ∀ w : Plc E, ((p : 𝓞 E) ∈ w.asIdeal → pLoc E w (finiteAdeleMap ℚ E e) = 1) ∧
    ((p : 𝓞 E) ∉ w.asIdeal → pLoc E w (finiteAdeleMap ℚ E e) = 0)

def AdTEx : Prop := ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [NumberField E] [IsCMField E], Nonempty (AdT p E)

def IsMu {R E : Type} [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] {n : ℕ}
    (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) : Prop :=
  ∀ (r : R) (x : Matrix (Fin n) (Fin n) E) i k, μ (r ⊗ₜ x) i k = r ⊗ₜ x i k

def MuEx : Prop := ∀ (R E : Type) [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] (n : ℕ),
  ∃ μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E), IsMu μ

def MuStar : Prop := ∀ (R E : Type) [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
  (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)), IsMu μ → ∀ x,
  Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E)) * μ (starT (hermStar (A.H n) (A.det_ne n)) R x).unop =
    ((μ x).map (conjT E R))ᵀ * Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E))

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsIso (A : Arith E) (n : ℕ) (a : GL (Fin n) (Af E)) : Prop :=
  (a.val.map (conjFin (conjE E)))ᵀ * Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E)) * a.val = 1 ∧
    ∀ (w : Plc E) (q : ℕ), q.Prime → A.Good q → (q : 𝓞 E) ∈ w.asIdeal → GeneralLinearGroup.map (pLoc E w) a ∈ KGL w n

def Arith.β₀ (A : Arith E) (n : ℕ) : (Matrix (Fin n) (Fin n) E)ˣ :=
  GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal fun i => (A.dg n i : E)) (by
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro i _
    have := A.c_ne
    unfold Arith.dg; split_ifs <;> simp [this])

variable {A : Arith E} {n p : ℕ} [Fact p.Prime]

def Setup.mx (S : Setup A n p) (h : S.G.GAf) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E :=
  ((h : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] S.G.C)

structure Tr (S : Setup A n p) extends AdT p E where
  μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)
  mu : IsMu μ
  a : GL (Fin n) (Af E)
  iso : IsIso A n a
  j : GUf E n →* S.G.GAf
  j_mx : ∀ g, μ (S.mx (j g)) = (a * mat g * a⁻¹).val.map Φ
  j_sim : ∀ g, ((uSimR (AfP p) (j g) : (AfP p)ˣ) : AfP p) = ρ (sim g : AfQˣ)
  sec : S.G.GAf →* GUf E n
  j_sec : ∀ h, j (sec h) = h
  sec_p : ∀ h (w : Plc E), (p : 𝓞 E) ∈ w.asIdeal → comp w (sec h) = 1
  j_eq : ∀ g g', j g = j g' ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w g = comp w g'

def JEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : AdT p E) (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)), IsMu μ →
  ∀ a : GL (Fin n) (Af E), IsIso A n a → ∃ j : GUf E n →* S.G.GAf,
    (∀ g, μ (S.mx (j g)) = (a * mat g * a⁻¹).val.map T.Φ) ∧
    ∀ g, ((uSimR (AfP p) (j g) : (AfP p)ˣ) : AfP p) = T.ρ (sim g : AfQˣ)

def JEq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : AdT p E) (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)), IsMu μ →
  ∀ (a : GL (Fin n) (Af E)) (j : GUf E n →* S.G.GAf), (∀ g, μ (S.mx (j g)) = (a * mat g * a⁻¹).val.map T.Φ) →
  (∀ g g' : GUf E n, (∀ w, comp w g = comp w g') → g = g') ∧
  ∀ g g', j g = j g' ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w g = comp w g'

def JSurj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : AdT p E) (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)), IsMu μ →
  ∀ a : GL (Fin n) (Af E), IsIso A n a → ∀ h : S.G.GAf, ∃ g : GUf E n,
    μ (S.mx h) = (a * mat g * a⁻¹).val.map T.Φ ∧ ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w g = 1

def IsoEx' : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ), Odd n → ∃ a, IsIso A n a

def TrEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p),
  Odd n → Nonempty (Tr S)

def LocComm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Plc E) (hw : IsSplitAt w)
  (x : GL (Fin n) (w.adicCompletion E)) (g : GUf E n), comp w g = 1 → CertificateRingHomMap.loc hw x * g = g * CertificateRingHomMap.loc hw x

theorem apart_of_not_mem {w u : Plc E} (hw : (p : 𝓞 E) ∉ w.asIdeal) (hu : (p : 𝓞 E) ∈ u.asIdeal) : GlobalTheory.Cong.Apart u w := by
  intro h
  apply hw
  have h1 : (p : 𝓞 (maximalRealSubfield E)) ∈ (u.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    show algebraMap _ (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal
    simpa using hu
  rw [h] at h1
  have h2 : algebraMap _ (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal := h1
  simpa using h2

def Tr.at {S : Setup A n p} (T : Tr S) (hc : LocComm) (w : Plc E) (hw : IsSplitAt w) (hp : (p : 𝓞 E) ∉ w.asIdeal) :
    Loc S.G.GAf (GL (Fin n) (w.adicCompletion E)) where
  pr := (comp w).comp T.sec
  loc := T.j.comp (CertificateRingHomMap.loc hw)
  pr_loc x := by
    have := (T.j_eq (T.sec (T.j (CertificateRingHomMap.loc hw x))) (CertificateRingHomMap.loc hw x)).1 (T.j_sec _) w hp
    simpa using this
  comm x g h := by
    have := congrArg T.j (hc E n w hw x (T.sec g) h)
    simpa [T.j_sec] using this

def LatCoord : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)), IsMu μ →
  ∃ ν : AfP p ⊗[ℚ] VQ S.D ≃+ (Fin n → AfP p ⊗[ℚ] E),
    (∀ (r : AfP p) (v : Fin n → 𝓞 E) i, ν (r ⊗ₜ ((1 : ℚ) ⊗ₜ[ℤ] v)) i = r ⊗ₜ (v i : E)) ∧
    (∀ h v, ν (S.L.actG h v) = μ (S.mx h) *ᵥ ν v) ∧ ∀ v, v ∈ LaHat S.D ↔ ∀ i, ν v i ∈ OHat p E

def Cong1 (N : ℕ) (w : Plc E) (x : GL (Fin n) (w.adicCompletion E)) : Prop :=
  ∀ i k, Valued.v ((x.val - 1) i k) ≤ Valued.v (N : w.adicCompletion E)

def KNIff : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (g : GUf E n),
  ((∀ v ∈ LaHat S.D, S.L.actG (T.j g) v ∈ LaHat S.D) ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i k,
    Valued.v ((GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹)).val i k) ≤ 1) ∧
  ∀ N : ℕ, 0 < N → (S.L.CongOne N (T.j g) ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal →
    Cong1 N w (GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹)))

def StdForm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S), ∃ (B : DForm S.G) (x : (AfP p ⊗[ℚ] S.G.C)ˣ) (hx : Triv S.G (AfP p) B.β x 1) (e : GlobalTheory.LKCx.grp S.G B.β →* Gam0 E n),
    (∀ y, ((e y : Gam0 E n) : GL (Fin n) E × ℚˣ) = (y : S.G.Cˣ × ℚˣ)) ∧ ∀ y, GlobalTheory.LKCx.toAfF S.G B.β x 1 hx y = T.j (rat (e y))

def PInt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (y : Gam0 E n), inclG S.G 1 (locC S.G (y : GL (Fin n) E × ℚˣ)) ∈ LocalSmoothExtension.Kp S.G →
  (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat y) ∈ KGL w n) ∧
    ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∈ v.asIdeal → Valued.v (((sim (rat y) : AfQˣ) : AfQ) v) = 1

def ClsConj : Prop := ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (B : DForm G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
  (hx : Triv G (AfP p) B.β x t), ∃ (y₀ : G.Cˣ × ℚˣ) (h₀ : G.GAf × Gr G 1)
    (e : GlobalTheory.LKCx.grp G (Quot.out (Quot.mk _ B : DFCls G)).β →* GlobalTheory.LKCx.grp G B.β),
    (∀ γ, ((e γ : GlobalTheory.LKCx.grp G B.β) : G.Cˣ × ℚˣ) = y₀⁻¹ * γ * y₀) ∧
    ∀ γ, (Quot.out (Quot.mk _ B : DFCls G)).emb γ = h₀ * B.embAt x t hx (e γ) * h₀⁻¹

end UpperTheory.Gal.W2.Seed
