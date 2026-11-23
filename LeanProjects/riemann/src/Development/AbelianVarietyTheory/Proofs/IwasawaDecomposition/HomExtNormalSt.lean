import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.AnalyticForms.RegularLocalRings.LogResStC

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam
open scoped CategoryTheory.Obj Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

section Branches

variable {X X' : Scheme.{0}}

def pre (π : X' ⟶ X) (Z : Closeds X) : Closeds X' := Z.preimage π.continuous

@[simp] theorem mem_pre {π : X' ⟶ X} {Z : Closeds X} {x : X'} : x ∈ pre π Z ↔ π x ∈ Z := Iff.rfl

theorem pre_comp {X'' : Scheme.{0}} (π' : X'' ⟶ X') (π : X' ⟶ X) (Z : Closeds X) :
    pre (π' ≫ π) Z = pre π' (pre π Z) := by
  first
  | rfl
  | (ext x; simp [mem_pre])

abbrev van (Z : Closeds X) (x : X) : Ideal (X.presheaf.stalk x) :=
  FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal Z) x

def tr {x y : X} (h : x = y) : X.presheaf.stalk x →+* X.presheaf.stalk y :=
  (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom

@[simp] theorem tr_rfl (x : X) (a : X.presheaf.stalk x) : tr (rfl : x = x) a = a := by
  simp [tr, TopCat.Presheaf.stalkCongr]

def IsRsp {A : Type} [CommRing A] [IsLocalRing A] {ι : Type} [Fintype ι] (f : ι → A) : Prop :=
  IsRegularLocalRing A ∧ Ideal.span (Set.range f) = maximalIdeal A ∧ (Fintype.card ι : WithBot ℕ∞) = ringKrullDim A

def BrAt (B : Closeds X) (x : X) {m d : ℕ} (f : Fin m ⊕ Fin d → X.presheaf.stalk x) : Prop :=
  IsRsp f ∧ van B x = Ideal.span {∏ j, f (Sum.inl j)}

def HasBr (B : Closeds X) : Prop := ∀ x : X, ∃ (m d : ℕ) (f : Fin m ⊕ Fin d → X.presheaf.stalk x), BrAt B x f

def Unimod {m m' : ℕ} (a : Fin m → Fin m' → ℕ) : Prop :=
  ∀ (L : Type) [AddCommGroup L] (γ : Fin m → L), IsPartOfBasis γ → IsPartOfBasis (fun i => ∑ j, a j i • γ j)

def IsModif (π : X' ⟶ X) (B : Closeds X) : Prop :=
  LocallyOfFiniteType π ∧ IsIso (π ∣_ B.compl) ∧
    ∀ (x' : X') (m d : ℕ) (f : Fin m ⊕ Fin d → X.presheaf.stalk (π x')), BrAt B (π x') f →
      ∃ (m' d' : ℕ) (f' : Fin m' ⊕ Fin d' → X'.presheaf.stalk x') (a : Fin m → Fin m' → ℕ),
        BrAt (pre π B) x' f' ∧ Unimod a ∧
          ∀ j, Associated ((π.stalkMap x').hom (f (Sum.inl j))) (∏ i, f' (Sum.inl i) ^ a j i)

def ColAt (B : Closeds X) {ι : Type} (E : ι → Closeds X) (x : X) {m d : ℕ} (f : Fin m ⊕ Fin d → X.presheaf.stalk x)
    (c : Fin m → ι) : Prop :=
  BrAt B x f ∧ ∀ i, van (E i) x = Ideal.span {∏ j ∈ Finset.univ.filter (fun j => c j = i), f (Sum.inl j)}

def IsStrict (B : Closeds X) {ι : Type} (E : ι → Closeds X) : Prop :=
  ∀ x : X, ∃ (m d : ℕ) (f : Fin m ⊕ Fin d → X.presheaf.stalk x) (c : Fin m → ι), ColAt B E x f c ∧ Function.Injective c

def IsBary (r : ℕ) (B : Closeds X) {ι : Type} (E : Option ι → Closeds X) : Prop :=
  ∀ x : X, ∃ (m d : ℕ) (f : Fin m ⊕ Fin d → X.presheaf.stalk x) (c : Fin m → Option ι), ColAt B E x f c ∧
    (∀ j j', c j = c j' → c j ≠ none → j = j') ∧ (Finset.univ.filter fun j => c j = none).card ≤ r

def monId {ι : Type} [Fintype ι] (E : ι → Closeds X) (a : ι → ℕ) (x : X) : Ideal (X.presheaf.stalk x) :=
  ∏ i, van (E i) x ^ a i

def Pulls (π : X' ⟶ X) {ι ι' : Type} [Fintype ι'] (E : ι → Closeds X) (E' : ι' → Closeds X') (M : ι → ι' → ℕ) : Prop :=
  ∀ (x' : X') (i : ι), (van (E i) (π x')).map (π.stalkMap x').hom = monId E' (M i) x'

def IsCentre (B C : Closeds X) : Prop :=
  ∀ x ∈ C, ∃ (m d : ℕ) (f : Fin m ⊕ Fin d → X.presheaf.stalk x) (S : Finset (Fin m)),
    BrAt B x f ∧ S.Nonempty ∧ van C x = Ideal.span ((fun j => f (Sum.inl j)) '' S)

def blowMat {m m' : ℕ} (S : Finset (Fin m)) (σ : Fin m' ↪ Fin m) (i₀ : Fin m') (j : Fin m) (i : Fin m') : ℕ :=
  if j = σ i ∨ (i = i₀ ∧ j ∈ S) then 1 else 0

def BlowRel {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') {m m' : ℕ} (f : Fin m → A) (S : Finset (Fin m))
    (f' : Fin m' → A') (σ : Fin m' ↪ Fin m) (i₀ : Fin m') : Prop :=
  σ i₀ ∈ S ∧ (∀ j ∉ S, j ∈ Set.range σ) ∧ ∀ j, Associated (φ (f j)) (∏ i, f' i ^ blowMat S σ i₀ j i)

def IsBlow (π : X' ⟶ X) (B C : Closeds X) : Prop :=
  IsIso (π ∣_ C.compl) ∧
    ∀ (x' : X') (m d : ℕ) (f : Fin m ⊕ Fin d → X.presheaf.stalk (π x')) (S : Finset (Fin m)), BrAt B (π x') f →
      S.Nonempty → van C (π x') = Ideal.span ((fun j => f (Sum.inl j)) '' S) →
      ∃ (m' d' : ℕ) (f' : Fin m' ⊕ Fin d' → X'.presheaf.stalk x') (σ : Fin m' ↪ Fin m) (i₀ : Fin m'),
        BrAt (pre π B) x' f' ∧ BlowRel (π.stalkMap x').hom (fun j => f (Sum.inl j)) S (fun i => f' (Sum.inl i)) σ i₀

def newCol (π : X' ⟶ X) (C : Closeds X) {ι : Type} (E : ι → Closeds X) : Option ι → Closeds X'
  | none => pre π C
  | some i => Closeds.closure (π ⁻¹' ((E i : Set X) \ C))

def ExtAt {U Y : Scheme.{0}} (j : U ⟶ X) (g : U ⟶ Y) (π : X' ⟶ X) (x' : X') : Prop :=
  ∃ (V : X'.Opens) (h : V.toScheme ⟶ Y), x' ∈ V ∧
    ∀ (T : Scheme.{0}) (a : T ⟶ V.toScheme) (u : T ⟶ U), a ≫ V.ι ≫ π = u ≫ j → a ≫ h = u ≫ g

def LocRes (B : Closeds X) {U : Scheme.{0}} (j : U ⟶ X) {I : Type} {Y : I → Scheme.{0}} (g : ∀ i, U ⟶ Y i) : Prop :=
  ∀ x ∈ B, ∃ (m d : ℕ) (f : Fin m ⊕ Fin d → X.presheaf.stalk x) (A : Finset (Fin m → ℕ)), BrAt B x f ∧
    ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (x' : X') (h : x = π x'), IsModif π B →
      (∀ a ∈ A, ∀ b ∈ A, (π.stalkMap x').hom (tr h (∏ j, f (Sum.inl j) ^ a j)) ∣
          (π.stalkMap x').hom (tr h (∏ j, f (Sum.inl j) ^ b j)) ∨
        (π.stalkMap x').hom (tr h (∏ j, f (Sum.inl j) ^ b j)) ∣ (π.stalkMap x').hom (tr h (∏ j, f (Sum.inl j) ^ a j))) →
      ∀ i, ExtAt j (g i) π x'

def IsChart (B : Closeds X) {k : Type} [Field k] {m d : ℕ} (ξ : Sp (ChartRing k m d) ⟶ X) : Prop :=
  IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
  (van B (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom = Ideal.span {∏ i, bdParam k m d i} ∧
  ∀ p : Sp (ChartRing k m d), ξ p ∈ B ↔ ∏ i, bdParam k m d i ∈ p.asIdeal

end Branches

section Pairs

variable {K F : Type} [Field K] [Field F] {XK X X'K X' : Scheme.{0}}

def IsPair (k : K →+* F) (sK : XK ⟶ Sp K) (s : X ⟶ Sp F) (e : X ⟶ XK) (BK : Closeds XK) : Prop :=
  CharZero K ∧ k.Finite ∧ IsProjOver sK ∧ IsPullback e s sK (spMap k) ∧ HasBr (pre e BK)

def IsMod (k : K →+* F) (sK : XK ⟶ Sp K) (s : X ⟶ Sp F) (e : X ⟶ XK) (BK : Closeds XK) (πK : X'K ⟶ XK) (π : X' ⟶ X)
    (e' : X' ⟶ X'K) : Prop :=
  IsPair k (πK ≫ sK) (π ≫ s) e' (pre πK BK) ∧ e' ≫ πK = π ≫ e ∧ IsIso (πK ∣_ BK.compl) ∧ IsModif π (pre e BK)

theorem IsMod.pre_eq {k : K →+* F} {sK : XK ⟶ Sp K} {s : X ⟶ Sp F} {e : X ⟶ XK} {BK : Closeds XK} {πK : X'K ⟶ XK}
    {π : X' ⟶ X} {e' : X' ⟶ X'K} (h : IsMod k sK s e BK πK π e') (Z : Closeds XK) :
    pre e' (pre πK Z) = pre π (pre e Z) := by
  rw [← pre_comp, h.2.1, pre_comp]

end Pairs

section Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsCN (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] : Prop :=
  IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsAdicComplete (maximalIdeal R) R ∧ CharZero R

def FineData {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) : Prop :=
  ∀ y : D.X, ∃ (μ₀ : D.X) (r : R), PsiCoord D (y + N • μ₀) r ∧ ∀ μ : D.X, ∃ s : R, PsiCoord D (y + N • μ) (r * s)

abbrev toBase {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') : Over.mk (spMap φ) ⟶ Over.mk (𝟙 (Sp R)) :=
  Over.homMk (spMap φ) (Category.comp_id _)

def IndepAlong {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (b : Fin n → LB.Sec (LPow G L (N : ℤ) T)) : Prop :=
  ∀ c c' s, Lin G L N h b c s → Lin G L N h b c' s → c = c'

def FreeSec {R : Type} [CommRing R] (t : SAB H (Sp R)) (N : ℕ) : Prop :=
  ∃ (n : ℕ) (b : Fin n → LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (𝟙 (Sp R))))),
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ φ : R →+* W, Function.Injective φ →
      BasisAlong t.G t.PP.L N (toBase φ) b

def AmpAt {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) (m : ℕ) : Prop :=
  ∃ (Z : Scheme.{0}) (π : Z ⟶ Y.X) (t : SAB H Z) (_ : SABMap t Y.t π), IsFinite π ∧ Surjective π ∧
    Nonempty (AmpFrames t.G t.PP.L (m ^ 2))

def IsCover {O F I : Type} [CommRing O] [Field F] (β : O →+* F) (R : I → Type) [∀ i, CommRing (R i)] (a : I → O)
    (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) : Prop :=
  IsDedFrac β ∧ (∀ i, IsDedFrac (ω i) ∧ (ω i).comp (b i) = β ∧ @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) ∧
    Ideal.span (Set.range a) = ⊤

end Sections

section Steps

def RspSt : Prop :=
  (∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Type) [Fintype J] (f : J → A), IsRsp f →
    (∀ S : Finset J, (Ideal.span (f '' S)).IsPrime ∧ (Ideal.span {∏ j ∈ S, f j}).IsRadical ∧
      ∀ j ∉ S, f j ∉ Ideal.span (f '' S)) ∧ ∀ j, Prime (f j)) ∧
  ∀ (A : Type) [CommRing A] [IsLocalRing A] (m d m' d' : ℕ) (f : Fin m ⊕ Fin d → A) (g : Fin m' ⊕ Fin d' → A),
    IsRsp f → IsRsp g → Ideal.span {∏ j, f (Sum.inl j)} = Ideal.span {∏ j, g (Sum.inl j)} →
    ∃ σ : Fin m ≃ Fin m', ∀ j, Associated (f (Sum.inl j)) (g (Sum.inl (σ j)))

def VanSt : Prop :=
  (∀ (X : Scheme.{0}) (Z : Closeds X) (x : X), (van Z x).IsRadical ∧ (x ∉ Z → van Z x = ⊤) ∧
    ∀ p : PrimeSpectrum (X.presheaf.stalk x), X.fromSpecStalk x p ∈ Z ↔ van Z x ≤ p.asIdeal) ∧
  (∀ (X : Scheme.{0}) (Z Z' : Closeds X) (x : X), van (Z ⊓ Z') x = (van Z x ⊔ van Z' x).radical) ∧
  (∀ (X X' : Scheme.{0}) (π : X' ⟶ X) (Z : Closeds X) (x' : X'),
    van (pre π Z) x' = ((van Z (π x')).map (π.stalkMap x').hom).radical) ∧
  ∀ (X X' : Scheme.{0}) (π : X' ⟶ X) (J : X.IdealSheafData) (x' : X'),
    FinalTheorems.stalkId (J.comap π) x' = (FinalTheorems.stalkId J (π x')).map (π.stalkMap x').hom

def VanBCSt : Prop :=
  ∀ (K F : Type) [Field K] [Field F] (k : K →+* F) (XK X : Scheme.{0}) (sK : XK ⟶ Sp K) (s : X ⟶ Sp F) (e : X ⟶ XK),
    CharZero K → k.Finite → IsPullback e s sK (spMap k) →
    Etale e ∧ IsFinite e ∧ Surjective e ∧
    (∀ Z : Closeds XK, (Scheme.IdealSheafData.vanishingIdeal Z).comap e = Scheme.IdealSheafData.vanishingIdeal (pre e Z)) ∧
    ∀ x : X, (e.stalkMap x).hom.Flat ∧ (maximalIdeal _).map (e.stalkMap x).hom = maximalIdeal _

def SncSt : Prop :=
  ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (B : Closeds X),
    (FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) ↔ HasBr B) ∧
    (HasBr B → Dense ((B : Set X)ᶜ) ∧ FinalTheorems.EffCartier (Scheme.IdealSheafData.vanishingIdeal B))

def UnimodSt : Prop :=
  (∀ (m m' : ℕ) (σ : Fin m ≃ Fin m'), Unimod (fun j i => if σ j = i then 1 else 0)) ∧
  (∀ (m m' m'' : ℕ) (a : Fin m → Fin m' → ℕ) (a' : Fin m' → Fin m'' → ℕ), Unimod a → Unimod a' →
    Unimod (fun j i => ∑ k, a j k * a' k i)) ∧
  ∀ (m m' : ℕ) (S : Finset (Fin m)) (σ : Fin m' ↪ Fin m) (i₀ : Fin m'), σ i₀ ∈ S → (∀ j ∉ S, j ∈ Set.range σ) →
    Unimod (blowMat S σ i₀)

def ModBasicSt : Prop :=
  (∀ (X X' : Scheme.{0}) (π : X' ⟶ X) (B : Closeds X) (x' : X') (m d : ℕ) (f : Fin m ⊕ Fin d → X.presheaf.stalk (π x')),
    IsIso (π.stalkMap x') → BrAt B (π x') f → BrAt (pre π B) x' (fun j => (π.stalkMap x').hom (f j))) ∧
  (∀ (X X' : Scheme.{0}) (π : X' ⟶ X) (B : Closeds X), IsIso π → IsModif π B) ∧
  (∀ (X X' X'' : Scheme.{0}) (π : X' ⟶ X) (π' : X'' ⟶ X') (B : Closeds X), IsModif π B → IsModif π' (pre π B) →
    IsModif (π' ≫ π) B) ∧
  (∀ (K F : Type) [Field K] [Field F] (k : K →+* F) (XK X : Scheme.{0}) (sK : XK ⟶ Sp K) (s : X ⟶ Sp F) (e : X ⟶ XK)
    (BK : Closeds XK), IsPair k sK s e BK → IsMod k sK s e BK (𝟙 _) (𝟙 _) e) ∧
  ∀ (K F : Type) [Field K] [Field F] (k : K →+* F) (XK X X'K X' X''K X'' : Scheme.{0}) (sK : XK ⟶ Sp K) (s : X ⟶ Sp F)
    (e : X ⟶ XK) (BK : Closeds XK) (πK : X'K ⟶ XK) (π : X' ⟶ X) (e' : X' ⟶ X'K) (πK' : X''K ⟶ X'K) (π' : X'' ⟶ X')
    (e'' : X'' ⟶ X''K), IsMod k sK s e BK πK π e' → IsMod k (πK ≫ sK) (π ≫ s) e' (pre πK BK) πK' π' e'' →
    IsMod k sK s e BK (πK' ≫ πK) (π' ≫ π) e''

def BlowProjSt : Prop :=
  ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (X : Scheme.{0}) (s : X ⟶ Sp O) (J : X.IdealSheafData), IsProjOver s →
    ∃ (X' : Scheme.{0}) (π : X' ⟶ X), FinalTheorems.Blowup π J ∧ IsProjOver (π ≫ s)

def BlowBCSt : Prop :=
  (∀ (X X' Y Y' : Scheme.{0}) (π : X' ⟶ X) (g : Y ⟶ X) (π' : Y' ⟶ Y) (g' : Y' ⟶ X') (J : X.IdealSheafData),
    FinalTheorems.Blowup π J → Flat g → IsPullback g' π' π g → FinalTheorems.Blowup π' (J.comap g)) ∧
  (∀ (X X' : Scheme.{0}) (π : X' ⟶ X) (J : X.IdealSheafData), FinalTheorems.Blowup π J → FinalTheorems.EffCartier J → IsIso π) ∧
  ∀ (X X' : Scheme.{0}) (π : X' ⟶ X) (J : X.IdealSheafData) (U : X.Opens), FinalTheorems.Blowup π J →
    Disjoint (U : Set X) (J.support : Set X) → IsIso (π ∣_ U)

def BlowStalkSt : Prop :=
  ∀ (X X' : Scheme.{0}) (π : X' ⟶ X) (J : X.IdealSheafData) (x' : X') (n : ℕ) (g : Fin n → X.presheaf.stalk (π x')),
    FinalTheorems.Blowup π J → FinalTheorems.stalkId J (π x') = Ideal.span (Set.range g) →
    ∃ (i : Fin n) (ψ : FinalTheorems.reesChart g i →+* X'.presheaf.stalk x') (q : Ideal (FinalTheorems.reesChart g i)) (_ : q.IsPrime),
      ψ.comp (algebraMap _ _) = (π.stalkMap x').hom ∧
      @IsLocalization.AtPrime _ _ (X'.presheaf.stalk x') _ ψ.toAlgebra q _

def ReesAlgSt : Prop :=
  ∀ (A A' : Type) [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A'] (m d n : ℕ) (f : Fin m ⊕ Fin d → A)
    (τ : Fin n ↪ Fin m) (i : Fin n) (ψ : FinalTheorems.reesChart (fun k => f (Sum.inl (τ k))) i →+* A')
    (q : Ideal (FinalTheorems.reesChart (fun k => f (Sum.inl (τ k))) i)) (_ : q.IsPrime), IsRsp f →
    @IsLocalization.AtPrime _ _ A' _ ψ.toAlgebra q _ → IsLocalHom (ψ.comp (algebraMap A _)) →
    ∃ (m' d' : ℕ) (f' : Fin m' ⊕ Fin d' → A') (σ : Fin m' ↪ Fin m) (i₀ : Fin m'), IsRsp f' ∧
      BlowRel (ψ.comp (algebraMap A _)) (fun j => f (Sum.inl j)) (Finset.univ.map τ) (fun i => f' (Sum.inl i)) σ i₀

def BlowLocSt : Prop :=
  ∀ (X X' : Scheme.{0}) (π : X' ⟶ X) (B C : Closeds X),
    FinalTheorems.Blowup π (Scheme.IdealSheafData.vanishingIdeal C) → IsBlow π B C

def CentreBlowSt : Prop :=
  ∀ (K F : Type) [Field K] [Field F] (k : K →+* F) (XK X : Scheme.{0}) (sK : XK ⟶ Sp K) (s : X ⟶ Sp F) (e : X ⟶ XK)
    (BK C : Closeds XK), IsPair k sK s e BK → IsCentre (pre e BK) (pre e C) →
    ∃ (X'K X' : Scheme.{0}) (πK : X'K ⟶ XK) (π : X' ⟶ X) (e' : X' ⟶ X'K),
      IsMod k sK s e BK πK π e' ∧ IsBlow π (pre e BK) (pre e C)

def ColSt : Prop :=
  (∀ (X X' : Scheme.{0}) [IsLocallyNoetherian X'] (π : X' ⟶ X) (B C : Closeds X) (J : Type) (E : J → Closeds X) (x' : X')
    (m d : ℕ) (f : Fin m ⊕ Fin d → X.presheaf.stalk (π x')) (c : Fin m → J), IsIso (π ∣_ C.compl) →
    ColAt B E (π x') f c →
    (π x' ∉ C → IsIso (π.stalkMap x') ∧
      ColAt (pre π B) (newCol π C E) x' (fun j => (π.stalkMap x').hom (f j)) (fun j => some (c j))) ∧
    ∀ (S : Finset (Fin m)) (m' d' : ℕ) (f' : Fin m' ⊕ Fin d' → X'.presheaf.stalk x') (σ : Fin m' ↪ Fin m) (i₀ : Fin m'),
      van C (π x') = Ideal.span ((fun j => f (Sum.inl j)) '' S) → BrAt (pre π B) x' f' →
      BlowRel (π.stalkMap x').hom (fun j => f (Sum.inl j)) S (fun i => f' (Sum.inl i)) σ i₀ →
      ColAt (pre π B) (newCol π C E) x' f' (fun i => if i = i₀ then none else some (c (σ i)))) ∧
  ∀ (K F : Type) [Field K] [Field F] (k : K →+* F) (XK X X'K X' : Scheme.{0}) (sK : XK ⟶ Sp K) (s : X ⟶ Sp F)
    (e : X ⟶ XK) (BK C : Closeds XK) (πK : X'K ⟶ XK) (π : X' ⟶ X) (e' : X' ⟶ X'K) (J : Type) (E : J → Closeds XK),
    IsMod k sK s e BK πK π e' →
    IsLocallyNoetherian X' ∧ ∀ o, pre e' (newCol πK C E o) = newCol π (pre e C) (fun i => pre e (E i)) o

def BaryCentreSt : Prop :=
  ∀ (K F : Type) [Field K] [Field F] (k : K →+* F) (XK X : Scheme.{0}) (sK : XK ⟶ Sp K) (s : X ⟶ Sp F) (e : X ⟶ XK)
    (BK : Closeds XK) (J : Type) (E : Option J → Closeds XK) (r : ℕ), IsPair k sK s e BK → 1 ≤ r →
    IsBary r (pre e BK) (fun i => pre e (E i)) →
    ∃ C : Closeds XK, ∀ (x : X) (m d : ℕ) (f : Fin m ⊕ Fin d → X.presheaf.stalk x) (c : Fin m → Option J),
      ColAt (pre e BK) (fun i => pre e (E i)) x f c →
      (Finset.univ.filter fun j => c j = none).card ≤ r ∧
      (x ∈ pre e C ↔ (Finset.univ.filter fun j => c j = none).card = r) ∧
      (x ∈ pre e C → van (pre e C) x = Ideal.span ((fun j => f (Sum.inl j)) '' (Finset.univ.filter fun j => c j = none)))

def BaryStepSt : Prop :=
  ∀ (K F : Type) [Field K] [Field F] (k : K →+* F) (XK X : Scheme.{0}) (sK : XK ⟶ Sp K) (s : X ⟶ Sp F) (e : X ⟶ XK)
    (BK : Closeds XK) (J : Type) [Fintype J] (E : Option J → Closeds XK) (r : ℕ), IsPair k sK s e BK →
    IsBary (r + 1) (pre e BK) (fun i => pre e (E i)) →
    ∃ (X'K X' : Scheme.{0}) (πK : X'K ⟶ XK) (π : X' ⟶ X) (e' : X' ⟶ X'K) (J' : Type) (_ : Fintype J')
      (E' : Option J' → Closeds X'K), IsMod k sK s e BK πK π e' ∧ IsBary r (pre e' (pre πK BK)) (fun i => pre e' (E' i))

def BarySt : Prop :=
  ∀ (K F : Type) [Field K] [Field F] (k : K →+* F) (XK X : Scheme.{0}) (sK : XK ⟶ Sp K) (s : X ⟶ Sp F) (e : X ⟶ XK)
    (BK : Closeds XK), IsPair k sK s e BK →
    ∃ (X'K X' : Scheme.{0}) (πK : X'K ⟶ XK) (π : X' ⟶ X) (e' : X' ⟶ X'K) (J' : Type) (_ : Fintype J')
      (E' : J' → Closeds X'K), IsMod k sK s e BK πK π e' ∧ IsStrict (pre e' (pre πK BK)) (fun i => pre e' (E' i))

def PairStepSt : Prop :=
  ∀ (K F : Type) [Field K] [Field F] (k : K →+* F) (XK X : Scheme.{0}) (sK : XK ⟶ Sp K) (s : X ⟶ Sp F) (e : X ⟶ XK)
    (BK : Closeds XK) (J : Type) [Fintype J] (E : J → Closeds XK) (i j : J), i ≠ j → IsPair k sK s e BK →
    IsStrict (pre e BK) (fun i => pre e (E i)) →
    ∃ (X'K X' : Scheme.{0}) (πK : X'K ⟶ XK) (π : X' ⟶ X) (e' : X' ⟶ X'K) (E' : Option J → Closeds X'K),
      IsMod k sK s e BK πK π e' ∧ IsStrict (pre e' (pre πK BK)) (fun i => pre e' (E' i)) ∧
      Pulls π (fun i => pre e (E i)) (fun o => pre e' (E' o))
        (fun a o => if o = some a ∨ (o = none ∧ (a = i ∨ a = j)) then 1 else 0) ∧
      (∀ x' : X', ¬ (e' x' ∈ E' (some i) ∧ e' x' ∈ E' (some j))) ∧
      (∀ (x' : X') (a : J), e' x' ∈ E' (some a) → e (π x') ∈ E a) ∧
      ∀ x' : X', e' x' ∈ E' none → e (π x') ∈ E i ∧ e (π x') ∈ E j

def OrderSt : Prop :=
  ∀ (K F : Type) [Field K] [Field F] (k : K →+* F) (XK X : Scheme.{0}) (sK : XK ⟶ Sp K) (s : X ⟶ Sp F) (e : X ⟶ XK)
    (BK : Closeds XK) (J : Type) [Fintype J] (E : J → Closeds XK) (A : Finset (J → ℕ)), IsPair k sK s e BK →
    IsStrict (pre e BK) (fun i => pre e (E i)) →
    ∃ (X'K X' : Scheme.{0}) (πK : X'K ⟶ XK) (π : X' ⟶ X) (e' : X' ⟶ X'K) (J' : Type) (_ : Fintype J')
      (E' : J' → Closeds X'K) (M : J → J' → ℕ),
      IsMod k sK s e BK πK π e' ∧ IsStrict (pre e' (pre πK BK)) (fun i => pre e' (E' i)) ∧
      Pulls π (fun i => pre e (E i)) (fun o => pre e' (E' o)) M ∧
      ∀ (x' : X'), ∀ a ∈ A, ∀ b ∈ A,
        (monId (fun i => pre e (E i)) a (π x')).map (π.stalkMap x').hom ≤
          (monId (fun i => pre e (E i)) b (π x')).map (π.stalkMap x').hom ∨
        (monId (fun i => pre e (E i)) b (π x')).map (π.stalkMap x').hom ≤
          (monId (fun i => pre e (E i)) a (π x')).map (π.stalkMap x').hom

def LocResPullSt : Prop :=
  ∀ (X X' U : Scheme.{0}) (π : X' ⟶ X) (B : Closeds X) (j : U ⟶ X) (j' : U ⟶ X') (I : Type) (Y : I → Scheme.{0})
    (g : ∀ i, U ⟶ Y i), IsModif π B → j' ≫ π = j → LocRes B j g → LocRes (pre π B) j' g

def ResolveColSt : Prop :=
  ∀ (K F : Type) [Field K] [Field F] (k : K →+* F) (XK X : Scheme.{0}) (sK : XK ⟶ Sp K) (s : X ⟶ Sp F) (e : X ⟶ XK)
    (BK : Closeds XK) (J : Type) [Fintype J] (E : J → Closeds XK) (U : Scheme.{0}) (j : U ⟶ X) (I : Type) [Finite I]
    (Y : I → Scheme.{0}) (g : ∀ i, U ⟶ Y i), IsPair k sK s e BK → IsStrict (pre e BK) (fun i => pre e (E i)) →
    IsOpenImmersion j → Set.range j = (pre e BK : Set X)ᶜ → LocRes (pre e BK) j g →
    ∃ (X'K X' : Scheme.{0}) (πK : X'K ⟶ XK) (π : X' ⟶ X) (e' : X' ⟶ X'K),
      IsMod k sK s e BK πK π e' ∧ ∀ i x', ExtAt j (g i) π x'

def ResolveSt : Prop :=
  ∀ (K F : Type) [Field K] [Field F] (k : K →+* F) (XK X : Scheme.{0}) (sK : XK ⟶ Sp K) (s : X ⟶ Sp F) (e : X ⟶ XK)
    (BK : Closeds XK) (U : Scheme.{0}) (j : U ⟶ X) (I : Type) [Finite I]
    (Y : I → Scheme.{0}) (g : ∀ i, U ⟶ Y i), IsPair k sK s e BK →
    IsOpenImmersion j → Set.range j = (pre e BK : Set X)ᶜ → LocRes (pre e BK) j g →
    ∃ (X'K X' : Scheme.{0}) (πK : X'K ⟶ XK) (π : X' ⟶ X) (e' : X' ⟶ X'K),
      IsMod k sK s e BK πK π e' ∧ ∀ i x', ExtAt j (g i) π x'

def GlueSt : Prop :=
  ∀ (X X' U Y : Scheme.{0}) (π : X' ⟶ X) (j : U ⟶ X) (g : U ⟶ Y), IsReduced X' → IsOpenImmersion j →
    Dense (π ⁻¹' Set.range j) → Y.IsSeparated → (∀ x', ExtAt j g π x') →
    ∃ h : X' ⟶ Y, ∀ (T : Scheme.{0}) (a : T ⟶ X') (u : T ⟶ U), a ≫ π = u ≫ j → a ≫ h = u ≫ g

def ExtAtSt : Prop :=
  ∀ (X X' U Y S : Scheme.{0}) [IsLocallyNoetherian X'] (π : X' ⟶ X) (j : U ⟶ X) (g : U ⟶ Y) (sX : X ⟶ S) (sY : Y ⟶ S)
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X') (y : Sp (FractionRing R) ⟶ U) (χ : Sp R ⟶ Y),
    IsOpenImmersion j → IsSeparated sY → LocallyOfFiniteType sY → g ≫ sY = j ≫ sX →
    (Scheme.stalkClosedPointTo ξ).hom.Flat → y ≫ j = jK R ≫ ξ ≫ π → jK R ≫ χ = y ≫ g → χ ≫ sY = ξ ≫ π ≫ sX →
    ExtAt j g π (ξ (closedPoint R))

def ModSmoothSt : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (X X' : Scheme.{0}) (s : X ⟶ Sp F) (π : X' ⟶ X) (B : Closeds X) (n : ℕ),
    SmoothOfRelativeDimension n s → HasBr B → IsModif π B →
    SmoothOfRelativeDimension n (π ≫ s) ∧ HasBr (pre π B)

def CohenSt : Prop :=
  ∀ (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℚ A] (m d : ℕ) (f : Fin m ⊕ Fin d → A), IsRsp f →
    IsAdicComplete (maximalIdeal A) A →
    ∃ (k : Type) (_ : Field k) (e : ChartRing k m d ≃+* A), ∀ i, e (MvPowerSeries.X i) = f i

def ChartLiftSt : Prop :=
  ∀ (X X' : Scheme.{0}) (π : X' ⟶ X) (B : Closeds X) (k : Type) [Field k] [CharZero k] (m d : ℕ)
    (ξ : Sp (ChartRing k m d) ⟶ X) (x' : X') (m' d' : ℕ) (f' : Fin m' ⊕ Fin d' → X'.presheaf.stalk x'),
    LocallyOfFiniteType π → IsIso (π ∣_ B.compl) → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom →
    ξ (closedPoint _) = π x' → BrAt (pre π B) x' f' →
    ∃ (k' : Type) (_ : Field k') (ξ' : Sp (ChartRing k' m' d') ⟶ X') (φ : ChartRing k m d →+* ChartRing k' m' d')
      (h : x' = ξ' (closedPoint _)), IsChart (pre π B) ξ' ∧ Function.Injective φ ∧ IsLocalHom φ ∧
      ξ' ≫ π = spMap φ ≫ ξ ∧ (∀ i, (Scheme.stalkClosedPointTo ξ').hom (tr h (f' i)) = MvPowerSeries.X i) ∧
      ∀ (h₁ : ξ (closedPoint _) = π x') (a : X.presheaf.stalk (ξ (closedPoint _))),
        φ ((Scheme.stalkClosedPointTo ξ).hom a) = (Scheme.stalkClosedPointTo ξ').hom (tr h ((π.stalkMap x').hom (tr h₁ a)))

def MatchSt : Prop :=
  ∀ (X : Scheme.{0}) (B : Closeds X) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ X), HasBr B →
    IsChart B ξ → ∃ (d₁ : ℕ) (f : Fin m ⊕ Fin d₁ → X.presheaf.stalk (ξ (closedPoint _))), BrAt B _ f ∧
      ∀ j, Associated ((Scheme.stalkClosedPointTo ξ).hom (f (Sum.inl j))) (bdParam k m d j)

def ProjDescSt : Prop :=
  ∀ (K F : Type) [Field K] [Field F] (k : K →+* F) (XK X : Scheme.{0}) (sK : XK ⟶ Sp K) (s : X ⟶ Sp F) (e : X ⟶ XK),
    CharZero K → k.Finite → IsPullback e s sK (spMap k) → IsProjOver s → IsProjOver sK

def JoinSchSt : Prop :=
  ∀ (O F I : Type) [CommRing O] [Field F] [Finite I] (β : O →+* F) (R : I → Type) [∀ i, CommRing (R i)] (a : I → O)
    (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) (X' : Scheme.{0}) (s' : X' ⟶ Sp F) (P : I → Scheme.{0})
    (p : ∀ i, P i ⟶ Sp (R i)) (h : ∀ i, X' ⟶ P i), IsCover β R a b ω → IsProjOver s' → Geo.Tor.IsNormalScheme X' →
    (∀ i, IsProjOver (p i)) → (∀ i, h i ≫ p i = s' ≫ spMap (ω i)) →
    ∃ (X : Scheme.{0}) (s : X ⟶ Sp O) (ε : pullback s (spMap β) ≅ X') (f : ∀ i, pullback s (spMap (b i)) ⟶ P i),
      Geo.Tor.IsNormalScheme X ∧ IsProjOver s ∧ Flat s ∧ ε.hom ≫ s' = pullback.snd _ _ ∧
      ∀ i, f i ≫ p i = pullback.snd _ _ ∧
        ∀ g : X' ⟶ pullback s (spMap (b i)), g ≫ pullback.fst _ _ = ε.inv ≫ pullback.fst _ _ → g ≫ f i = h i

def AbOpenSt : Prop := ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → IsOpen (abLocus G)

def HomExtNormalSt : Prop :=
  ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), Geo.Tor.IsNormalScheme X → IsOpenImmersion j → IsDominant j →
    ∀ (G G' : Over X) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' →
    ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G', IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f

def SabExtNormalSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X),
    Geo.Tor.IsNormalScheme X → IsOpenImmersion j → IsDominant j →
    ∀ (t₀ : SAB H U) (t t' : SAB H X) (a : SABMap t₀ t j) (a' : SABMap t₀ t' j), IsProper t₀.G.hom →
      ∃ b : SABMap t t' (𝟙 X), a.φ ≫ b.φ = a'.φ

def CmpSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β)
    (Z : Model Xo c β') (ρ : gen Z ⟶ gen Y), Z.jQ ≫ ρ = Y.jQ → Geo.Tor.IsNormalScheme (gen Z) →
    ∃ (t₀ : SAB H (gen Z)) (n₁ : SABMap t₀ Z.t (genι Z)) (n₂ : SABMap t₀ Y.t (ρ ≫ genι Y)),
      ∀ (T : Scheme.{0}) (g : T ⟶ t₀.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
        g ≫ t₀.G.hom = g₁ ≫ Z.oF.t.G.hom ≫ Z.jQ → g ≫ n₁.φ = g₁ ≫ Z.m.φ →
        g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom → g ≫ n₂.φ = g₂ ≫ Y.m.φ

def DescSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), Y.Descends →
    ∃ (XK : Scheme.{0}) (sK : XK ⟶ Sp (KA l)) (e : gen Y ⟶ XK) (BK : Closeds XK),
      IsPullback e (genStr Y) sK (spMap (IntermediateField.inclusion c.le).toRingHom) ∧ genBd Y = pre e BK ∧
      ∀ (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z : Model Xo c β') (ρ : gen Z ⟶ gen Y) (X'K : Scheme.{0})
        (πK : X'K ⟶ XK) (e' : gen Z ⟶ X'K), Z.jQ ≫ ρ = Y.jQ → Geo.Tor.IsNormalScheme (gen Z) →
        IsPullback e' (genStr Z) (πK ≫ sK) (spMap (IntermediateField.inclusion c.le).toRingHom) → e' ≫ πK = ρ ≫ e →
        IsIso (πK ∣_ BK.compl) → Z.Descends

def DomTransSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' O'' : Type) [CommRing O] [CommRing O'] [CommRing O''] (β : O →+* c.F) (β' : O' →+* c.F)
    (β'' : O'' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (Y'' : Model Xo c β'') (b : O →+* O') (b' : O' →+* O''),
    β''.comp b' = β' → β'.comp b = β → Dominates Y Y' b → Dominates Y' Y'' b' → Dominates Y Y'' (b'.comp b)

def CoverSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ Xo : ∀ l : Level H, Moduli D l, ∃ Y : LocFam Xo,
      (∀ p W hp hW, N2 (Y p W hp hW) ∧ ∀ i, (Y p W hp hW i).SplitFibres ∧ (Y p W hp hW i).N3 ∧ (Y p W hp hW i).N4) ∧
      ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p),
        ∃ (I : Type) (_ : Finite I) (R : I → Type) (_ : ∀ i, CommRing (R i)) (a : I → 𝓞 c.F) (b : ∀ i, 𝓞 c.F →+* R i)
          (ω : ∀ i, R i →+* c.F) (C : ∀ i, Model (Xo l) c (ω i)),
          IsCover (algebraMap (𝓞 c.F) c.F) R a b ω ∧ (∀ i, Amp (C i)) ∧
          ∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b₀ : 𝓞 c.F →+* c.V W),
            (∀ x, ((b₀ x : c.V W) : c.F) = (x : c.F)) →
            ∃ (i : I) (b' : R i →+* c.V W), b'.comp (b i) = b₀ ∧ (c.V W).subtype.comp b' = ω i ∧
              Dominates (C i) (Y p W hp hW ⟨l, c, hg p hp⟩) b'

def JoinSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O₀ : Type) [CommRing O₀] (β₀ : O₀ →+* c.F) (Y : Model Xo c β₀) (I : Type) [Finite I] (R : I → Type)
    [∀ i, CommRing (R i)] (a : I → 𝓞 c.F) (b : ∀ i, 𝓞 c.F →+* R i) (ω : ∀ i, R i →+* c.F) (C : ∀ i, Model Xo c (ω i))
    (X' : Scheme.{0}) (π : X' ⟶ gen Y) (h : ∀ i, X' ⟶ gen (C i)),
    IsCover (algebraMap (𝓞 c.F) c.F) R a b ω → IsProjOver (π ≫ genStr Y) → Geo.Tor.IsNormalScheme X' →
    IsIso (π ∣_ (genBd Y).compl) → Dense (π ⁻¹' Set.range Y.jQ) →
    (∀ i (T : Scheme.{0}) (v : T ⟶ X') (u : T ⟶ Xo.XF c), v ≫ π = u ≫ Y.jQ → v ≫ h i = u ≫ (C i).jQ) →
    ∃ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (ε : gen Z ≅ X'), Z.jQ ≫ ε.hom ≫ π = Y.jQ ∧
      ε.hom ≫ π ≫ genStr Y = genStr Z ∧ ∀ i, Dominates Z (C i) (b i)

def BdSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsDedFrac β →
    FinalTheorems.EffCartier (genBdIdeal Y) →
    ∃ (Z : Model Xo c β) (ε : gen Z ≅ gen Y) (BD : EffCartierData Z.X), Z.jQ ≫ ε.hom = Y.jQ ∧
      ε.hom ≫ genStr Y = genStr Z ∧ Dominates Z Y (RingHom.id O) ∧
      (∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Z.t.G) ∧ ∀ x ∈ genBd Z, genι Z x ∈ BD.idealSheaf.support

def PullSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [CommRing R'] [IsDomain R'] [IsLocalRing R'] (φ : R →+* R') (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t),
    IsCN R → IsCN R' → Function.Injective φ → IsLocalHom φ → P.TorsionIso →
    ∃ (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap φ)) (P' : PELUnif (maximalIdeal R') t')
      (e : P'.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X), P'.TorsionIso ∧
      ∀ y r, PsiCoord P.D.toPre (e y) r → ∃ u : R'ˣ, PsiCoord P'.D.toPre y (u * φ r)

def FineSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (m : ℕ) (t : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ D.X)
    (N : ℕ), 1 ≤ N → IsMonomial D t β →
    ∃ A : Finset (Fin m → ℕ), ∀ (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R') (D' : DegPre R') (e : D'.X ≃+ D.X),
      (∀ y r, PsiCoord D (e y) r → ∃ u : R'ˣ, PsiCoord D' y (u * φ r)) →
      (∀ a ∈ A, ∀ b ∈ A, φ (∏ j, t j ^ a j) ∣ φ (∏ j, t j ^ b j) ∨ φ (∏ j, t j ^ b j) ∣ φ (∏ j, t j ^ a j)) →
      FineData D' N

def FreeClosedSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (N : ℕ), IsCN R → 1 ≤ N → FineData P.D.toPre N →
    ∃ (n : ℕ) (b : Fin n → LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (𝟙 (Sp R))))),
      BasisAlong t.G t.PP.L N (toBase (algebraMap R (FractionRing R))) b ∧ IndepAlong t.G t.PP.L N (toBase (residue R)) b

def IndepSpreadSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsLocalRing R]
    (t : SAB H (Sp R)) (N n : ℕ) (b : Fin n → LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (𝟙 (Sp R))))),
    IndepAlong t.G t.PP.L N (toBase (residue R)) b →
    ∀ (k : Type) [Field k] (φ : R →+* k), IndepAlong t.G t.PP.L N (toBase φ) b

def FreeTraitSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (t : SAB H (Sp R)) (_ : PELUnif (maximalIdeal R) t) (N n : ℕ)
    (b : Fin n → LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (𝟙 (Sp R))))),
    BasisAlong t.G t.PP.L N (toBase (algebraMap R (FractionRing R))) b →
    (∀ (k : Type) [Field k] (φ : R →+* k), IndepAlong t.G t.PP.L N (toBase φ) b) →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ φ : R →+* W, Function.Injective φ →
      BasisAlong t.G t.PP.L N (toBase φ) b

def FreeSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (N : ℕ), IsCN R → 1 ≤ N → FineData P.D.toPre N → FreeSec t N

theorem freeSt_of (h₁ : FreeClosedSt) (h₂ : IndepSpreadSt) (h₃ : FreeTraitSt) : FreeSt := by
  intro E _ _ _ H R _ _ _ t P N hR hN hF
  obtain ⟨n, b, hb, hi⟩ := h₁ E H R t P N hR hN hF
  refine ⟨n, b, ?_⟩
  intro W _ _ _ hW φ hφ
  exact h₃ E H R t P N n b hb (fun k _ ψ => h₂ E H R t N n b hi k ψ) W hW φ hφ

def ExtendSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (C : Model Xo c β)
    (Y : Model Xo c β') (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R))
    (_ : SABMap t Y.t ξ) (y : Sp (FractionRing R) ⟶ Xo.XF c) (b : O →+* R) (m : ℕ), IsCN R → y ≫ Y.j = jK R ≫ ξ →
    y ≫ C.j ≫ C.s = jK R ≫ spMap b → AmpAt C m → FreeSec t 1 → FreeSec t (m ^ 2) →
    ∃ χ : Sp R ⟶ C.X, jK R ≫ χ = y ≫ C.j

def LiftTorSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (k : Type) [Field k] (m d : ℕ)
    (ξ : Sp (ChartRing k m d) ⟶ gen Y) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t)
    (γ : Fin m → levelForms H l.M' P.D.toPre.X) (X' : Scheme.{0}) (π : X' ⟶ gen Y) (x' : X'),
    HasBr (genBd Y) → IsToricChart Y ξ P γ → IsModif π (genBd Y) → ξ (closedPoint _) = π x' →
    ∃ (k' : Type) (_ : Field k') (m' d' : ℕ) (ξ' : Sp (ChartRing k' m' d') ⟶ X')
      (φ : ChartRing k m d →+* ChartRing k' m' d') (t' : SAB H (Sp (ChartRing k' m' d')))
      (_ : SABMap t' Y.t (ξ' ≫ π ≫ genι Y)) (P' : PELUnif (maximalIdeal (ChartRing k' m' d')) t')
      (γ' : Fin m' → levelForms H l.M' P'.D.toPre.X) (e : P'.D.toPre.X ≃+ P.D.toPre.X) (h : x' = ξ' (closedPoint _)),
      (∀ (h₁ : ξ (closedPoint _) = π x') (a : (gen Y).presheaf.stalk (ξ (closedPoint _))),
        φ ((Scheme.stalkClosedPointTo ξ).hom a) =
          (Scheme.stalkClosedPointTo ξ').hom (tr h ((π.stalkMap x').hom (tr h₁ a)))) ∧ IsChart (pre π (genBd Y)) ξ' ∧ IsCN (ChartRing k' m' d') ∧ ξ' ≫ π = spMap φ ≫ ξ ∧
      P'.TorsionIso ∧ IsMonomial P'.D.toPre (bdParam k' m' d') (fun i => γ' i) ∧ IsPartOfBasis γ' ∧
      ∀ y r, PsiCoord P.D.toPre (e y) r → ∃ u : (ChartRing k' m' d')ˣ, PsiCoord P'.D.toPre y (u * φ r)

def CritSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (I : Type) [Finite I] (R : I → Type)
    [∀ i, CommRing (R i)] (ω : ∀ i, R i →+* c.F) (C : ∀ i, Model Xo c (ω i)),
    HasBr (genBd Y) → (∀ x ∈ genBd Y, HasToricChart Y x) → (∀ i, Amp (C i)) →
    LocRes (genBd Y) Y.jQ (fun i => (C i).jQ)

def FinSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β)
    (Z : Model Xo c β') (ρ : gen Z ⟶ gen Y), Z.jQ ≫ ρ = Y.jQ → Geo.Tor.IsNormalScheme (gen Z) → IsModif ρ (genBd Y) →
    HasBr (genBd Y) → (∀ x ∈ genBd Y, HasToricChart Y x) →
    genBd Z = pre ρ (genBd Y) ∧ ∀ x ∈ genBd Z, HasToricChart Z x

end Steps

end GlobalTheory.TorRef
