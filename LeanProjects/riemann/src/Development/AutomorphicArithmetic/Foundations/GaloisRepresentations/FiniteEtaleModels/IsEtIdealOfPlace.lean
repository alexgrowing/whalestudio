import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES

namespace UpperTheory.Gal.FiniteEtaleModels

def IsEtIdeal {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] (b : Base D R) (𝔞 : Ideal (𝓞 D.F)) : Prop :=
  𝔞 ≠ ⊥ ∧ ∀ w : Ideal (𝓞 D.F), w.IsMaximal → 𝔞 ≤ w → IsEtPlace b w

def RepLev {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R}
    (o : Obj b N s) (𝔞 : Ideal (𝓞 D.F)) (r : ℕ) : Prop :=
  ∃ (Y : Scheme.{0}) (π : Y ⟶ S) (lu : D.La → (Over.mk π ⟶ o.A)), IsFinite π ∧ Etale π ∧ IsEtLevOver o 𝔞 r lu ∧
    ∀ (T : Over S) (l : D.La → (T ⟶ o.A)), IsEtLevOver o 𝔞 r l → ∃! f : T ⟶ Over.mk π, ∀ y, f ≫ lu y = l y

def FinCover : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (𝔞 : Ideal (𝓞 D.F)) (r : ℕ), 3 ≤ N → N.Coprime p → IsEtIdeal b 𝔞 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Scheme.{0}) (π : Y ⟶ S) (o' : Obj b N (π ≫ s)) (m : ObjMap o' o π) (lv : D.La → (𝟙_ (Over Y) ⟶ o'.A)) (ρ : LevGrp D 𝔞 r → (Y ⟶ Y)), IsEtLev o' 𝔞 r lv ∧ GlobalTheory.ZM.IsGaloisCover (LevGrp D 𝔞 r) ρ π ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (o₁ : Obj b N (t ≫ s)) (m₁ : ObjMap o₁ o t) (l : D.La → (𝟙_ (Over T) ⟶ o₁.A)), IsEtLev o₁ 𝔞 r l → ∃! f : T ⟶ Y, f ≫ π = t ∧ ∃ m₂ : ObjMap o₁ o' f, ∀ y, (l y).left ≫ m₂.φ = f ≫ (lv y).left

def FinModel : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (𝔞 : Ideal (𝓞 D.F)) (r : ℕ), IsEtIdeal b 𝔞 → ∀ M : Model b N, ∃ (E : EtModel b N 𝔞 r) (π : E.X ⟶ M.X) (ρ : LevGrp D 𝔞 r → (E.X ⟶ E.X)), π ≫ M.s = E.s ∧ Nonempty (ObjMap E.univ M.univ π) ∧ GlobalTheory.ZM.IsGaloisCover (LevGrp D 𝔞 r) ρ π

def FinFet : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (𝔞 : Ideal (𝓞 D.F)) (r : ℕ), IsEtIdeal b 𝔞 → ∀ (M : Model b N) (E : EtModel b N 𝔞 r) (π : E.X ⟶ M.X), π ≫ M.s = E.s → Nonempty (ObjMap E.univ M.univ π) → IsFinite π ∧ Etale π ∧ Surjective π

def FinHecke : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (𝔞 : Ideal (𝓞 D.F)) (r : ℕ), IsEtIdeal b 𝔞 → ∀ (E : EtModel b N 𝔞 r) (E' : EtModel b (N * k) 𝔞 r), ∃ π : E'.X ⟶ E.X, π ≫ E.s = E'.s ∧ IsFinite π ∧ Etale π ∧ ∃ (o' : Obj b N E'.s) (ψ : E'.univ.A ⟶ o'.A), IsHecke g c k N E'.univ o' ψ ∧ ∃ m : ObjMap o' E.univ π, ∀ y, (E'.lv y ≫ ψ).left ≫ m.φ = π ≫ (E.lv y).left

def FinForget : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p), 3 ≤ N → ∀ (𝔞 : Ideal (𝓞 D.F)) (r : ℕ), IsEtIdeal b 𝔞 → ∀ (E : EtModel b N 𝔞 r) (E' : EtModel b N' 𝔞 r), ∃ π : E'.X ⟶ E.X, π ≫ E.s = E'.s ∧ IsFinite π ∧ Etale π ∧ ∃ m : ObjMap (E'.univ.forget N hd hc) E.univ π, ∀ y, (E'.lv y).left ≫ m.φ = π ≫ (E.lv y).left

def CrtMul : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (𝔞 𝔟 : Ideal (𝓞 D.F)), 𝔞 ⊔ 𝔟 = ⊤ → ∀ (T : Over S) (l₁ l₂ : D.La → (T ⟶ o.A)),
    IsEtLevOver o 𝔞 1 l₁ → IsEtLevOver o 𝔟 1 l₂ → IsEtLevOver o (𝔞 * 𝔟) 1 fun y => l₁ y * l₂ y

def CrtProj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (𝔞 𝔟 : Ideal (𝓞 D.F)) (e : 𝓞 D.F), e ∈ 𝔟 → 1 - e ∈ 𝔞 → ∀ (T : Over S) (l : D.La → (T ⟶ o.A)),
    IsEtLevOver o (𝔞 * 𝔟) 1 l → IsEtLevOver o 𝔞 1 fun y => l (algebraMap (𝓞 D.F) D.O e • y)

def RepMul : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (𝔞 𝔟 : Ideal (𝓞 D.F)), 𝔞 ⊔ 𝔟 = ⊤ → RepLev o 𝔞 1 → RepLev o 𝔟 1 → RepLev o (𝔞 * 𝔟) 1

def IdealInd : Prop :=
  ∀ (A : Type) [CommRing A] [IsDedekindDomain A] (Q P : Ideal A → Prop), P ⊤ → (∀ (w : Ideal A) (r : ℕ), w.IsMaximal → Q w → P (w ^ r)) →
    (∀ 𝔞 𝔟 : Ideal A, 𝔞 ⊔ 𝔟 = ⊤ → P 𝔞 → P 𝔟 → P (𝔞 * 𝔟)) →
    ∀ 𝔞 : Ideal A, 𝔞 ≠ ⊥ → (∀ w : Ideal A, w.IsMaximal → 𝔞 ≤ w → Q w) → P 𝔞

def RepAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (𝔞 : Ideal (𝓞 D.F)) (r : ℕ), N.Coprime p → IsEtIdeal b 𝔞 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), RepLev o 𝔞 r

def PtAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (𝔞 : Ideal (𝓞 D.F)) (r : ℕ), N.Coprime p → IsEtIdeal b 𝔞 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ l : D.La → (Over.mk x ⟶ o.A), IsEtLevOver o 𝔞 r l

def PPow : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (𝔞 : Ideal (𝓞 D.F)), IsEtIdeal b 𝔞 → ∃ e : ℕ, ((p ^ e : ℕ) : 𝓞 D.F) ∈ 𝔞

def GrpFin : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (𝔞 : Ideal (𝓞 D.F)) (r : ℕ), 𝔞 ≠ ⊥ → Finite (D.La ⧸ wSub D 𝔞 r) ∧ Finite (LevGrp D 𝔞 r)

def LevHecke : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ) (𝔞 : Ideal (𝓞 D.F)) (r : ℕ), k.Coprime p → (∃ e : ℕ, ((p ^ e : ℕ) : 𝓞 D.F) ∈ 𝔞) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (o' : Obj b N s) (ψ : o.A ⟶ o'.A) (lv : D.La → (𝟙_ (Over S) ⟶ o.A)), IsHecke g c k N o o' ψ → IsEtLev o 𝔞 r lv → IsEtLev o' 𝔞 r (fun y => lv y ≫ ψ)

def PlaceOf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (b : Base D O)
    (r : ℤ) (w : Ideal (𝓞 D.F)), w.IsMaximal → (p : O) ∈ IsLocalRing.maximalIdeal O → D.a = 1 → uIdeal D r ≤ w →
    (∀ i, ∀ x ∈ w, b.t i x ∈ IsLocalRing.maximalIdeal O) →
    ∀ 𝔞 : Ideal (𝓞 D.F), 𝔞 ⊔ w = ⊤ → (IsEtIdeal b 𝔞 ↔ ∃ e : ℕ, uIdeal D r ^ e ≤ 𝔞)

end UpperTheory.Gal.FiniteEtaleModels
