import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.CompactBIffCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsGHeckeMapForget
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Definitions.Divisors.HxiTZeroComb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtC GlobalTheory.UPel.HT GlobalTheory.PELU GlobalTheory.KS
open scoped TensorProduct Matrix

namespace GlobalTheory.EtaleLevelHecke

def ModelExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → Nonempty (Model b N)

def ModelProj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.CompactB → ∀ M : Model b N, IsProjOver M.s

def HeckeFet : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (M : Model b N) (M' : Model b (N * k)), ∃ π : M'.X ⟶ M.X, IsHeckeMap g c k N M.toRepFam M'.toRepFam π ∧ IsFinite π ∧ Etale π ∧ Surjective π

def EtLevCover : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), 3 ≤ N → N.Coprime p → IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Scheme.{0}) (π : Y ⟶ S) (o' : Obj b N (π ≫ s)) (m : ObjMap o' o π) (lv : D.La → (𝟙_ (Over Y) ⟶ o'.A)) (ρ : LevGrp D w0 r → (Y ⟶ Y)), IsEtLev o' w0 r lv ∧ GlobalTheory.ZM.IsGaloisCover (LevGrp D w0 r) ρ π ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (o₁ : Obj b N (t ≫ s)) (m₁ : ObjMap o₁ o t) (l : D.La → (𝟙_ (Over T) ⟶ o₁.A)), IsEtLev o₁ w0 r l → ∃! f : T ⟶ Y, f ≫ π = t ∧ ∃ m₂ : ObjMap o₁ o' f, ∀ y, (l y).left ≫ m₂.φ = f ≫ (lv y).left

def EtLevModel : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ M : Model b N, ∃ (E : EtModel b N w0 r) (π : E.X ⟶ M.X) (ρ : LevGrp D w0 r → (E.X ⟶ E.X)), π ≫ M.s = E.s ∧ Nonempty (ObjMap E.univ M.univ π) ∧ GlobalTheory.ZM.IsGaloisCover (LevGrp D w0 r) ρ π

def EtLevHecke : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (E : EtModel b N w0 r) (E' : EtModel b (N * k) w0 r), ∃ π : E'.X ⟶ E.X, π ≫ E.s = E'.s ∧ IsFinite π ∧ Etale π ∧ ∃ (o' : Obj b N E'.s) (ψ : E'.univ.A ⟶ o'.A), IsHecke g c k N E'.univ o' ψ ∧ ∃ m : ObjMap o' E.univ π, ∀ y, (E'.lv y ≫ ψ).left ≫ m.φ = π ≫ (E.lv y).left

def EtLevForget : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p), 3 ≤ N → ∀ (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (E : EtModel b N w0 r) (E' : EtModel b N' w0 r), ∃ π : E'.X ⟶ E.X, π ≫ E.s = E'.s ∧ IsFinite π ∧ Etale π ∧ ∃ m : ObjMap (E'.univ.forget N hd hc) E.univ π, ∀ y, (E'.lv y).left ≫ m.φ = π ≫ (E.lv y).left

def GenExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R' : Type) [CommRing R'] [Algebra ℚ R'] [IsNoetherianRing R'] (gb : GBase D.toG R') (N : ℕ), 3 ≤ N → N.Coprime p → Nonempty (GenModel gb N)

def GenCmp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (R' : Type) [CommRing R'] [Algebra ℚ R'] (φ : R →+* R') (gb : GBase D.toG R'), gb.ρ = φ b.ρ → (∀ i, gb.t i = φ.comp (b.t i)) → ∀ (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (M : Model b N) (X : GenModel gb N), ∃ j : X.X ⟶ pullback M.s (spMap φ), IsOpenImmersion j ∧ IsClosedImmersion j ∧ j ≫ pullback.snd _ _ = X.s ∧ IsGPull X.univ M.univ (j ≫ pullback.fst _ _)

def GenHecke : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R' : Type) [CommRing R'] [Algebra ℚ R'] [IsNoetherianRing R'] (gb : GBase D.toG R') (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (X : GenModel gb N) (X' : GenModel gb (N * k)), ∃ π : X'.X ⟶ X.X, IsGHeckeMap g c k N X X' π ∧ IsFinite π ∧ Etale π ∧ Surjective π

def GenHeckeBC : Prop :=
  ∀ (G : GDatum) (R₁ R₂ : Type) [CommRing R₁] [CommRing R₂] [Algebra ℚ R₁] [Algebra ℚ R₂] (ψ : R₁ →+* R₂) (gb₁ : GBase G R₁) (gb₂ : GBase G R₂) (g : G.La →ₗ[G.O] G.La) (c k N : ℕ), 3 ≤ N → 0 < k → ∀ (X₁ : GenModel gb₁ N) (X₁' : GenModel gb₁ (N * k)) (X₂ : GenModel gb₂ N) (X₂' : GenModel gb₂ (N * k)) (π₁ : X₁'.X ⟶ X₁.X) (π₂ : X₂'.X ⟶ X₂.X) (j : X₂.X ⟶ pullback X₁.s (spMap ψ)) (j' : X₂'.X ⟶ pullback X₁'.s (spMap ψ)), IsGHeckeMap g c k N X₁ X₁' π₁ → IsGHeckeMap g c k N X₂ X₂' π₂ → j ≫ pullback.snd _ _ = X₂.s → j' ≫ pullback.snd _ _ = X₂'.s → IsGGPull X₂.univ X₁.univ (j ≫ pullback.fst _ _) → IsGGPull X₂'.univ X₁'.univ (j' ≫ pullback.fst _ _) → π₂ ≫ j ≫ pullback.fst _ _ = j' ≫ pullback.fst _ _ ≫ π₁

def GenCxPoint : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (gb : GBase D.toG ℂ) (N : ℕ), 3 ≤ N → N.Coprime p → gb.ρ = D.ρc → (∀ i (c : 𝓞 D.F), gb.t i c = D.tau i (c : D.F)) → ∀ X : GenModel gb N, ∃ x : Sp ℂ ⟶ X.X, x ≫ X.s = 𝟙 _

def UnifCx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (M : Model b N), 3 ≤ N → N.Coprime p → b.IsType σ ρ → M.Uniformised σ ρ

def UnifCxQuot : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (M : Model b N), 3 ≤ N → N.Coprime p → b.IsType σ ρ → IsProjOver M.s → ∃ (h : _) (hL : _) (U : Unif (M.univ.fam h hL) σ ρ N (D.Cls N)) (r : Fin U.n → ℕ) (bs : ∀ i, Module.Basis (Fin (r i)) ℤ (U.Di i).La), (∀ i, (Dom (U.Di i) (bs i)).Nonempty ∧ ContractibleSpace (Dom (U.Di i) (bs i)) ∧ DiscreteTopology (Gam (U.Di i) (bs i) N) ∧ (∀ x ∈ Gam (U.Di i) (bs i) N, IsOfFinOrder x → x = 1) ∧ ∃ K : Set (UG (U.Di i) (bs i) ℝ), IsCompact K ∧ ∀ x, ∃ q ∈ Gam (U.Di i) (bs i) N, q * x ∈ K) ∧ Nonempty (GlobalTheory.CxPts M.s σ ≃ₜ (Σ i, DomQuot (U.Di i) (bs i) (Gam (U.Di i) (bs i) N)))

def KSProj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (M : Model b N) (l : ℕ) [Fact l.Prime], l ≠ p → ∀ (E : Type) [Field E] [CharZero E] [Algebra ℚ_[l] E] (m : ℕ) (ε : Matrix (Fin m) (Fin m) D.O →₀ E) (k : ℕ), 3 ≤ N → N.Coprime p → b.IsType σ ρ → IsProjOver M.s → ArtinQE l E → IsCut (Module.toModuleEnd ℤ (S := D.O) D.La) ε k → ∀ n : ℕ, op l M.univ.act M.s (spMap σ) ε n * op l M.univ.act M.s (spMap σ) ε n = op l M.univ.act M.s (spMap σ) ε n

def Top : Prop :=
  ModelExists ∧ ModelProj ∧ HeckeFet ∧ EtLevCover ∧ EtLevModel ∧ EtLevHecke ∧ EtLevForget ∧ GenExists ∧ GenCmp ∧ GenHecke ∧ GenHeckeBC ∧ GenCxPoint ∧ UnifCx ∧ UnifCxQuot ∧ KSProj

end GlobalTheory.EtaleLevelHecke
