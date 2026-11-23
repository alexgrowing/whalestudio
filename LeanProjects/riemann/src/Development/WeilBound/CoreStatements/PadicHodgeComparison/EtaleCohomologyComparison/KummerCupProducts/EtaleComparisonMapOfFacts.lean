import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.MapUgCToUg

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.E

open CH GlobalTheory.EtC

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def eFam (hN : LcNat) (H : RIn l) (r : Roots l) (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : EtFam l K :=
  fun M n j => eM hN H r M n 0 j

def twUg (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) : (PAlg.tw σ A).Ug →+* A.Ug :=
  Localization.awayLift ((algebraMap A.U A.Ug).comp (PAlg.twU σ A)) (l : (PAlg.tw σ A).U) (by
    rw [RingHom.comp_apply, map_natCast]
    exact IsLocalization.Away.algebraMap_isUnit (l : A.U))

theorem twUg_algebraMap (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (x : (PAlg.tw σ A).U) :
    twUg σ A (algebraMap _ _ x) = algebraMap _ _ (PAlg.twU σ A x) := by
  unfold twUg
  rw [Localization.awayLift, IsLocalization.Away.lift_eq]
  rfl

def tCo {C : Type 1} [Category.{0} C] {P : PAlg l ⥤ Type} (G : C ⥤ El P) (n j : ℕ) (z : Cn (G ⋙ modF (AcrEl P n)) j) :
    Cn (G ⋙ modF (AcrEl P n)) j := (ACris.periodT (untilt_epsilon (p := l)) : Acris l) • z

def lcCo {C : Type 1} [Category.{0} C] (hN : LcNat) (H : RIn l) (r : Roots l) {P : PAlg l ⥤ Type} (G : C ⥤ El P) (n j : ℕ)
    (z : Cn (probe H r (G ⋙ CategoryOfElements.π _) n).L j) : Cn (G ⋙ modF (AcrEl P n)) j :=
  (lcMor hN H r (G ⋙ CategoryOfElements.π _) n).pullC j z

def LineData.IsBC {X' X : Scheme.{0}} (g : X' ⟶ X) (D : LineData X) (D' : LineData X') (π : D'.Y ⟶ D.Y) : Prop :=
  π ≫ D.f = D'.f ≫ g ∧ (∀ (V : Scheme.{0}) (a : V ⟶ D.Y) (x : V ⟶ X'), a ≫ D.f = x ≫ g → ∃ b : V ⟶ D'.Y, b ≫ π = a ∧ b ≫ D'.f = x) ∧
  ∀ (V : Scheme.{0}) (a b : V ⟶ D'.Y) h h', D'.u a b h = D.u (a ≫ π) (b ≫ π) h'

def LogAlg : Prop := ∀ (S : Type) [CommRing S] [Algebra ℚ S] (T : Subring S) (γ : ℕ → S → S),
  (∀ k x, γ k x = ((k.factorial : ℚ)⁻¹) • x ^ k) → ∀ x y : S, (∀ k, γ k x ∈ T) → (∀ k, γ k y ∈ T) →
  (∀ k, γ k (x + y + x * y) ∈ T) ∧ ∀ N : ℕ, ∃ c ∈ T,
    ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * γ (k + 1) (x + y + x * y) =
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * γ (k + 1) x +
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * γ (k + 1) y + (N.factorial : S) * c

def LineBC : Prop := ∀ (X' X : Scheme.{0}) (g : X' ⟶ X) (D : LineData X), ∃ (D' : LineData X') (π : D'.Y ⟶ D.Y), D.IsBC g D' π

def TwUg : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (σ : Gal(PadicAlgCl l/K)),
  (∀ (A B : PAlg l) (f : A ⟶ B), (twUg σ B).comp (PAlg.mapUg (PAlg.twMap σ f)) = (PAlg.mapUg f).comp (twUg σ A)) ∧
  (∀ (A : PAlg l) (x : PadicAlgCl l), twUg σ A (kb (PAlg.tw σ A) x) = kb A (σ x)) ∧
  ∀ (M : Model l K) (A : PAlg l) (y : M.P.obj A), geomPt M A y ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q σ =
    Spec.map (CommRingCat.ofHom (twUg σ A)) ≫
      geomPt M (PAlg.tw σ A) ((pxTw M.p (okToOC l K) σ (galOC_okToOC σ)).app A y)

def FRed : Prop := EtIn → ∀ (hN : LcNat) (l : ℕ) [Fact l.Prime] (H : RIn l) (r : Roots l) (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
  (eFam hN H r K).Red

def FEqui : Prop := EtIn → ∀ (hN : LcNat) (l : ℕ) [Fact l.Prime] (H : RIn l) (r : Roots l) (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
  (eFam hN H r K).Equi

def FPhi : Prop := ∀ (hN : LcNat) (l : ℕ) [Fact l.Prime] (H : RIn l) (r : Roots l) (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
  (eFam hN H r K).Phi

def FNat : Prop := EtIn → ∀ (hN : LcNat) (l : ℕ) [Fact l.Prime] (H : RIn l) (r : Roots l) (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
  (eFam hN H r K).Natu

def FRes : Prop := EtIn → ∀ (hN : LcNat) (l : ℕ) [Fact l.Prime] (H : RIn l) (r : Roots l) (K : IntermediateField ℚ_[l] (PadicAlgCl l))
  (M : Model l K) (C : Type 1) [Category.{0} C] (G : C ⥤ El M.P) (n : ℕ) (i : ℤ) (j : ℕ) (x : Ht (l ^ n) (sch.obj (gb M)) j i),
  (Mor.restrict (modF (AcrEl M.P n)) G).pull j (eM hN H r M n i j x) = eG hN H r M G n i j x

def FCup : Prop := EtIn → ∀ (hN : LcNat) (l : ℕ) [Fact l.Prime] (H : RIn l) (r : Roots l) (K : IntermediateField ℚ_[l] (PadicAlgCl l))
  (M : Model l K) (n : ℕ) (i i' i'' : ℤ) (hi : i + i' = i'') (j j' j'' : ℕ) (hj : j + j' = j'')
  (x : Ht (l ^ n) (sch.obj (gb M)) j i) (y : Ht (l ^ n) (sch.obj (gb M)) j' i'),
  eM hN H r M n i'' j'' ((cup (l ^ n) x y).cast (by omega) hi) =
    (mulP (AcrEl M.P n)).cup hj (eM hN H r M n i j x) (eM hN H r M n i' j' y)

def FRoot : Prop := EtIn → ∀ (hN : LcNat) (l : ℕ) [Fact l.Prime] (H : RIn l) (r : Roots l) (K : IntermediateField ℚ_[l] (PadicAlgCl l))
  (M : Model l K) (i : ℤ), ∃ v : Hl l (sch.obj (gb M)) (0 : ℕ) i, ∀ n, eM hN H r M n i 0 (v.1 n) = oneH (AcrEl M.P n)

def FUntw : Prop := EtIn → ∀ (hN : LcNat) (l : ℕ) [Fact l.Prime] (H : RIn l) (r : Roots l) (K : IntermediateField ℚ_[l] (PadicAlgCl l))
  (M : Model l K) (x : Hl l (sch.obj (gb M)) (2 : ℕ) 1), ∃ v : Hl l (sch.obj (gb M)) (2 : ℕ) 0,
    ∀ n, eM hN H r M n 0 2 (v.1 n) = eM hN H r M n 1 2 (x.1 n)

def FKum : Prop := ∀ (hN : LcNat) (l : ℕ) [Fact l.Prime] (H : RIn l) (r : Roots l) (K : IntermediateField ℚ_[l] (PadicAlgCl l))
  (M : Model l K) (D : LineData M.X) (D' : LineData (gb M)) (π : D'.Y ⟶ D.Y),
  D.IsBC (pullback.fst _ _ ≫ pullback.fst _ _ : gb M ⟶ M.X) D' π →
  ∀ (C : Type 1) [Category.{0} C] (G : C ⥤ El M.P) (Λ : Lift G D) (n : ℕ),
    ∃ z : Cn (probe H r (G ⋙ CategoryOfElements.π _) n).L 2, Nonempty (IsKumCoc (pts H r M G n) D' z) ∧
      Λ.IsCoc n (tCo G n 2 (lcCo hN H r G n 2 z))

def FirstChernClassFamily : Prop := EtIn → ∀ (hN : LcNat) (l : ℕ) [Fact l.Prime] (H : RIn l) (r : Roots l) (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
  (eFam hN H r K).C1

theorem etale_comparison_map_of_facts (h0 : RootsEx) (hN : LcNat) (h1 : FRed) (h2 : FEqui) (h3 : FPhi) (h4 : FNat) (h5 : FCup) (h6 : FRoot)
    (h7 : FirstChernClassFamily) : EtaleComparisonMapExists := by
  intro hE l _ H K
  obtain ⟨r⟩ := h0 l
  show ∃ e : EtFam l K, e.Good
  exact ⟨eFam hN H r K, ⟨h1 hE hN l H r K, h2 hE hN l H r K, h3 hN l H r K, h4 hE hN l H r K,
    fun M n i j x y => h5 hE hN l H r K M n 0 0 0 rfl i j (i + j) rfl x y,
    fun M => h6 hE hN l H r K M 0, h7 hE hN l H r K⟩⟩

end CrystallineSemistableComparison.E
