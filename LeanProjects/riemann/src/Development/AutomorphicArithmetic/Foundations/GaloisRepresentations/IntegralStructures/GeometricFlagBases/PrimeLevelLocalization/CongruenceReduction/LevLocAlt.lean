import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc GLw AfQ sim comp loc SameK IsCen cj)
open UpperTheory.Gal.W2.Seed (Arith Setup)
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.Int.Geo.Pl.Tj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def IntM (u : Plc E) (M : Matrix (Fin n) (Fin n) (u.adicCompletion E)) : Prop := ∀ i k, M i k ∈ u.adicCompletionIntegers E

structure Shp (x : E) (w : Plc E) (i : ℕ) (g : GUf E n) : Prop where
  at_w : IsT w i (comp w g)
  off : ∀ u, u ≠ w → ¬ SameK x (cj u) w → comp u g = 1
  cen : ∀ u, u ≠ cj w → SameK x (cj u) w →
    (comp u g).val = ((Ideal.absNorm w.asIdeal ^ i : ℕ) : u.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) _)
  int : ∀ u, IntM u (comp u g).val
  back : ∀ u, IntM u (((Ideal.absNorm w.asIdeal ^ i : ℕ) : u.adicCompletion E) • (comp u g⁻¹).val)
  sim : ∀ v : Plc ℚ, Valued.v (((sim g : AfQˣ) : AfQ) v) = Valued.v ((Ideal.absNorm w.asIdeal ^ i : ℕ) : v.adicCompletion ℚ)

def CjEnt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : GUf E n) (w : Plc E) (i k : Fin n),
    cj (cj w) = w ∧ Valued.v ((comp (cj w) g).val i k) =
      Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g : AfQˣ) : AfQ) w * (comp w g⁻¹).val k i)

def CjInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : GUf E n) (w : Plc E),
    (comp w g ∈ KGL w n → comp (cj w) g ∈ KGL (cj w) n → 0 < n →
      Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g : AfQˣ) : AfQ) w) = 1) ∧
    (Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g : AfQˣ) : AfQ) w) = 1 → comp w g ∈ KGL w n →
      comp (cj w) g ∈ KGL (cj w) n)

def ShpOf : Prop :=
  Sides → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (x : E), Gen A x → ∀ q : ℕ, q.Prime → A.SplitK q →
    ∀ w : Plc E, (q : 𝓞 E) ∈ w.asIdeal → ∀ (hw : IsSplitAt w) (i : ℕ), i ≤ n → ∀ (t : GLw n w) (z : GUf E n), IsT w i t → IsCen x w z →
      Shp x w i (loc hw t * z ^ i)

def AtSite (P : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
    (_F : Frame S) (N : Lv p) (w : Plc E) (_σ : Site S N w) (_i : ℕ) (_g : GUf E n), Prop) : Prop :=
  Sides → Dict → LevBasic → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime]
    (S : Setup A n p) (F : Frame S) (x : E), Gen A x → ∀ (N : Lv p) (w : Plc E) (σ : Site S N w) (i : ℕ), i ≤ n →
    ∀ g : GUf E n, Shp x w i g → P E A n p S F N w σ i g

def TCong : Prop := AtSite fun E _ _ _ _ _ _ _ S F _ w σ _ g =>
  (∀ m : ℕ, m.Coprime σ.q → S.L.CongOne m (F.j g)) ∧
    ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ⊔ w.asIdeal = ⊤ → (∃ e : ℕ, uId S.D σ.q σ.r ^ e ≤ 𝔞) → CongId S.L 𝔞 (F.j g)

def TKill : Prop := AtSite fun E _ _ _ _ _ _ _ S F _ w _ _ g =>
  ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∀ y ∈ w.asIdeal, ∀ v ∈ LaHat S.D, ∃ v' ∈ LaHat S.D, S.L.actG (F.j g) v' = mulF S.D (s * y) v

def TCard : Prop := AtSite fun _ _ _ _ _ _ _ _ S F _ w _ i g =>
  (((LaHat S.D).map (S.L.actG (F.j g)).toAddMonoidHom) ⊔ idHat S.D w.asIdeal).relIndex (LaHat S.D) = Ideal.absNorm w.asIdeal ^ i

def TMult : Prop := AtSite fun _ _ _ _ _ _ p _ S F _ w _ i g =>
  Integ S.L (F.j g) ∧ (∃ t t' : AfP p, IsIntAf t ∧ IsIntAf t' ∧ t * t' = 1 ∧
    F.ρ (sim g : AfQˣ) = ((Ideal.absNorm w.asIdeal ^ i : ℕ) : AfP p) * t) ∧
    ∀ v ∈ LaHat S.D, ∃ v' ∈ LaHat S.D, S.L.actG (F.j g) v' = (Ideal.absNorm w.asIdeal ^ i) • v

def LocIdx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Plc E) (i : ℕ), i ≤ n → ∀ t : GLw n w, IsT w i t →
    ∀ [w.asIdeal.IsMaximal], ((KGL w n).comap (MulAut.conj t).toMonoidHom).relIndex (KGL w n) =
      Nat.card (crystallineComparison.Gr (𝓞 E ⧸ w.asIdeal) (Fin n → 𝓞 E ⧸ w.asIdeal) i)

def LevLoc : Prop := AtSite fun _ _ _ _ _ n _ _ _ F _ w σ _ g =>
  (∀ k, F.j k ∈ σ.K₀ → comp w k ∈ KGL w n) ∧ (∀ κ ∈ KGL w n, ∃ k, F.j k ∈ σ.K₀ ∧ comp w k = κ) ∧
    ∀ k, F.j k ∈ σ.K₀ → (F.j (g * k * g⁻¹) ∈ σ.K₀ ↔ comp w (g * k * g⁻¹) ∈ KGL w n)

end UpperTheory.Gal.Int.Geo.Pl.Tj
