import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.VecCoord
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.InvTMemSim

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open GlobalTheory.LFun (KGL satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.W2.Seed

def TyLev.kerK {X M : Type} [Group X] [Group M] (T : TyLev X M) : Subgroup X :=
  ((T.ψ.comp ((T.L.pr.comp T.K.subtype).codRestrict T.J fun k => T.fact.2 k k.2)).ker).map T.K.subtype

theorem TyLev.mem_kerK {X M : Type} [Group X] [Group M] (T : TyLev X M) (k : X) :
    k ∈ T.kerK ↔ ∃ hk : k ∈ T.K, T.ψ ⟨T.L.pr k, T.fact.2 k hk⟩ = 1 :=
  ⟨fun ⟨y, hy, e⟩ => e ▸ ⟨y.2, hy⟩, fun ⟨hk, h⟩ => ⟨⟨k, hk⟩, h, rfl⟩⟩

theorem TyLev.triv_of_le {X M : Type} [Group X] [Group M] (T : TyLev X M) {K : Subgroup X} (h : K ≤ T.kerK) : T.Triv K :=
  ⟨fun k hk => ((T.mem_kerK k).1 (h hk)).1, fun k hk _ => ((T.mem_kerK k).1 (h hk)).2⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}

theorem th_eq (F : Frame S) : F.th = CertificateRingHomMap.th :=
  MonoidHom.ext fun g => Subtype.ext (Prod.ext (Units.ext (F.th_mat g)) (F.th_sim g))

def FacEq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (F : Frame S) (hc : LocComm) (w : Spl E p), IsFac F w (fac F.tr hc w) ∧ ∀ L, IsFac F w L → L = fac F.tr hc w

def LevSec : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (S₀ : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GLw n w)), (∀ u ∈ S₀, (p : 𝓞 E) ∉ u.asIdeal) →
  (∀ k ∈ lev S₀ Kw, T.sec (T.j k) ∈ lev S₀ Kw) ∧
  ∀ k : GUf E n, (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w k = 1) → (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k ∈ KGL w n) →
    (∀ u ∈ S₀, (1 : GLw n u) ∈ Kw u) → k ∈ lev S₀ Kw

def IsCongGrp (N : ℕ) (w : Plc E) (K : Subgroup (GLw n w)) : Prop := ∀ y, y ∈ K ↔ Cong1 N w y ∧ Cong1 N w y⁻¹

def CongGrpEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N : ℕ), 0 < N → ∀ w : Plc E, ∃ K : Subgroup (GLw n w),
  IsCongGrp N w K ∧ IsOpen (K : Set (GLw n w)) ∧ IsCompact (K : Set (GLw n w)) ∧ K ≤ KGL w n ∧
    (∀ a ∈ KGL w n, ∀ y, a * y * a⁻¹ ∈ K ↔ y ∈ K) ∧ ((N : 𝓞 E) ∈ w.asIdeal → K ≤ Iw n w) ∧ Iw n w ≤ KGL w n

def CongConj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N : ℕ) (w : Plc E) (g : GUf E n), sim g = 1 →
  Cong1 N w (comp w g)⁻¹ → Cong1 N (CertificateRingHomMap.cj w) (comp (CertificateRingHomMap.cj w) g)

def KNFact : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (F : Frame S) (w : Spl E p) (L : Loc S.G.GAf (GLw n w.1)), IsFac F w L → ∀ q : ℕ, q.Prime → A.Good q → (q : 𝓞 E) ∈ w.1.asIdeal →
  ∀ N : ℕ, 0 < N → ∀ K : Subgroup (GLw n w.1), IsCongGrp N w.1 K → L.Fact (S.L.KN N) K

def SiteFact : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (F : Frame S) (x : E), Gen A x → ∀ (N : Lv p) (w : Spl E p) (σ : Site S N w.1) (L : Loc S.G.GAf (GLw n w.1)), IsFac F w L →
  L.Fact σ.K₀ (KGL w.1 n)

def CuspTh : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Plc E) (σ : SmIrr (GLw n w)),
  ∃ σ' : SmIrr (GLw n w), ∃ e : σ.V ≃ₗ[ℂ] σ'.V, (∀ (g g' : GLw n w) v, g'.val = (g⁻¹).valᵀ → σ'.ρ g' (e v) = e (σ.ρ g v)) ∧
    (GlobalTheory.SmGL.IsCuspidal σ'.ρ → GlobalTheory.SmGL.IsCuspidal σ.ρ)

def Denom : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (h : G.GAf),
  ∃ c : ℕ, 0 < c ∧ c.Coprime p ∧ ∀ v ∈ LaHat D, c • L.actG h v ∈ LaHat D

def LocConj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w w' : Plc E) (hw : IsSplitAt w) (hw' : IsSplitAt w'),
  ¬ Apart w' w → ∀ y' : GLw n w', ∃ y : GLw n w, CertificateRingHomMap.loc hw' y' = CertificateRingHomMap.loc hw y

def CenFacts : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ), 0 < n → ∀ x : E, Gen A x →
  ∀ q : ℕ, q.Prime → A.SplitK q → ∀ w : Plc E, (q : 𝓞 E) ∈ w.asIdeal → ∀ z : GUf E n, IsCen x w z →
  (∀ g, z * g = g * z) ∧ ∀ u : Plc E, (q : 𝓞 E) ∉ u.asIdeal → comp u z = 1

def StabKer : Prop := ForData fun _ _ _ _ _ _ _ _ S F _ _ _ _ V r _ _ _ Ty => ∀ k, Stab F V k → k ∈ S.L.KN r → k ∈ Ty.kerK

def SeenShape : Prop := ForData fun E _ _ _ _ n p _ S F x U _ _ V r W N L Ty => ∀ (g : Mem S.L N) (θ : ℂ), Seen F V r g θ →
  g.K ≤ Ty.kerK ∧ ((IsDeckM g ∧ g.h ∈ Ty.kerK ∧ θ = 1) ∨
  ∃ (w : Spl E p) (t : GLw n w.1) (z : GUf E n) (i : ℕ) (B : Multiset ℂˣ), Free V w.1 ∧ (∀ u ∈ W, Apart w.1 u.1) ∧ i ≤ n ∧ IsT w.1 i t ∧
    IsCen x w.1 z ∧ SatU U w.1 B ∧ (∀ u : Plc E, (p : 𝓞 E) ∈ u.asIdeal → comp u z = 1) ∧
    g.h⁻¹ = (L w).loc t⁻¹ * F.j (z ^ i)⁻¹ ∧ Ty.Cen (F.j (z ^ i)⁻¹) ∧ (∀ u ∈ W, (L u).pr g.h = 1) ∧ (L w).Fact g.K (KGL w.1 n) ∧
    θ = (idx g : ℂ) * (satEig (Ideal.absNorm w.1.asIdeal) n B i * (((V.κ.val w.1 : ℂˣ) : ℂ)⁻¹) ^ i))

def SeenActs : Prop := ForData fun _ _ _ _ _ _ _ _ S F _ _ _ _ V r _ N _ Ty => ∀ (g : Mem S.L N) (θ : ℂ), Seen F V r g θ →
  (∀ a, g.fn a ≠ 0 → ∃ k ∈ Ty.K, g.h * k * a ∈ Ty.K) ∧
  (IsDeckM g → g.h ∈ Ty.kerK → Ty.Acts g.fn 1 1) ∧
  ∀ (M' : Type) [Group M'] (L' : Loc S.G.GAf M') (Kw : Subgroup M') (t : M') (z : S.G.GAf), L'.Fact Ty.K Kw → L'.Fact g.K Kw → Ty.L.Apart L' →
    Ty.Cen z → g.h⁻¹ = L'.loc t * z → Ty.Acts g.fn (idx g) g.h⁻¹

def ActsConv : Prop := ∀ (X M : Type) [Group X] [Group M] (T : TyLev X M) (ψ : X → ℂ) (c : ℂ) (h : X), T.Acts ψ c h →
  conv T.K₀ ψ (T.tf 1) = c • T.tf h ∧ ∀ (c' : ℂ) (h' : X), T.L.pr h' = 1 →
    conv T.K₀ ψ (c' • T.tf h') = (c * c') • conv T.K₀ (T.tf h) (T.tf h')

def TEig : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 0 < n → ∀ (x : E) (U : Submodule ℂ (UA E n → ℂ)) (w₀ : Plc E)
  (Up : Plc E → Prop) (V : Vec x U w₀ Up) (w : Plc E) (hw : IsSplitAt w), Free V w → ∀ (i : ℕ), i ≤ n → ∀ t, IsT w i t → ∀ z, IsCen x w z →
  ∀ B, SatU U w B → ∀ g : GUf E n,
    ∑ᶠ y : GLw n w ⧸ KGL w n, dosetInd ℂ (KGL w n) t⁻¹ y.out • V.Φ (CertificateRingHomMap.th (g * (z ^ i)⁻¹ * CertificateRingHomMap.loc hw y.out)) =
      (satEig (Ideal.absNorm w.asIdeal) n B i * (((V.κ.val w : ℂˣ) : ℂ)⁻¹) ^ i) • V.Φ (CertificateRingHomMap.th g)

def PhiTy : Prop := ForData fun E _ _ _ _ n p _ _ F _ _ _ _ V _ _ _ _ Ty =>
  (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) ≠ 0 ∧ Ty.IsTy (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) ∧
  (∀ g : GUf E n, (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w g ∈ KGL w n) → V.Φ (CertificateRingHomMap.th (F.tr.sec (F.j g))) = V.Φ (CertificateRingHomMap.th g)) ∧
  ∀ k : GUf E n, (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w k = 1) → (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k ∈ KGL w n) →
    ∀ g, V.Φ (CertificateRingHomMap.th (g * k)) = V.Φ (CertificateRingHomMap.th g)

end UpperTheory.Gal.W2.Seed
