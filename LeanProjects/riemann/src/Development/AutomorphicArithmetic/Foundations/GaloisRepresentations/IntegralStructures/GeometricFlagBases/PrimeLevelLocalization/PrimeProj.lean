import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PackExOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Geo.Pl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime]

structure Frame (S : Setup A n p) where
  j : GUf E n →* S.G.GAf
  surj : Function.Surjective j
  ker : ∀ g, j g = 1 ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w g = 1
  a : ∀ w : Plc E, GLw n w
  a_int : ∀ (w : Plc E) (q : ℕ), q.Prime → A.Good q → (q : 𝓞 E) ∈ w.asIdeal → a w ∈ KGL w n
  a_cof : ∀ᶠ w in Filter.cofinite, a w ∈ KGL w n
  vec : ∀ w : Plc E, AfP p ⊗[ℚ] VQ S.D →+ (Fin n → w.adicCompletion E)
  vec_inj : ∀ v, (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → vec w v = 0) → v = 0
  vec_hat : ∀ v, v ∈ LaHat S.D ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i, vec w v i ∈ w.adicCompletionIntegers E
  vec_surj : ∀ y : ∀ w : Plc E, Fin n → w.adicCompletion E, (∀ w i, y w i ∈ w.adicCompletionIntegers E) →
    ∃ v, ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → vec w v = y w
  vec_in : ∀ (w : Plc E), (p : 𝓞 E) ∉ w.asIdeal → ∀ (y : Fin n → 𝓞 E) i, vec w (inAf S.D y) i = algebraMap (𝓞 E) _ (y i)
  vec_act : ∀ (w : Plc E), (p : 𝓞 E) ∉ w.asIdeal → ∀ g v, vec w (S.L.actG (j g) v) = (a w * comp w g * (a w)⁻¹).val *ᵥ vec w v
  vec_mul : ∀ (w : Plc E), (p : 𝓞 E) ∉ w.asIdeal → ∀ (c : 𝓞 E) v,
    vec w (mulF S.D c v) = algebraMap (𝓞 E) (w.adicCompletion E) c • vec w v
  ρ : AfQ →+* AfP p
  ρ_int : ∀ s : AfQ, IsIntAf (ρ s) ↔ ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∉ v.asIdeal → Valued.v (s v) ≤ 1
  mult : ∀ g, (((j g : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) = ρ (sim g : AfQˣ)
  B : DForm S.G
  x : (AfP p ⊗[ℚ] S.G.C)ˣ
  t : (AfP p)ˣ
  hx : GlobalTheory.LKMid.Triv S.G (AfP p) B.β x t
  mem : ∀ y : GL (Fin n) E × ℚˣ, y ∈ GlobalTheory.LKCx.grp S.G B.β ↔ y ∈ Gam0 E n
  emb1 : ∀ (y : GL (Fin n) E × ℚˣ) (h : y ∈ GlobalTheory.LKCx.grp S.G B.β) (h' : y ∈ Gam0 E n), (B.embAt x t hx ⟨y, h⟩).1 = j (rat ⟨y, h'⟩)
  emb2 : ∀ (y : GL (Fin n) E × ℚˣ) (h : y ∈ GlobalTheory.LKCx.grp S.G B.β) (h' : y ∈ Gam0 E n),
    (B.embAt x t hx ⟨y, h⟩).2 ∈ LocalSmoothExtension.Kp S.G ↔ ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat ⟨y, h'⟩) ∈ KGL w n
  th : GUf E n →* GUf E n
  th_mat : ∀ g, (mat (th g)).val = ((mat g)⁻¹).valᵀ
  th_sim : ∀ g, sim (th g) = (sim g)⁻¹
  tr : UpperTheory.Gal.W2.Seed.Tr S
  j_tr : j = tr.j
  a_tr : ∀ w, a w = GeneralLinearGroup.map (pLoc E w) tr.a

structure Vec (x : E) (U : Submodule ℂ (UA E n → ℂ)) (w₀ : Plc E) (Up : Plc E → Prop) : Type 1 where
  π : AutSub E n
  hV : π.V = U
  W : Wt E n
  hW : π.finPart W ≠ ⊥
  m : InfinitePlace E → ℕ
  pos : ∀ v i, 0 ≤ (W v).w i + m v
  jz : ℤ
  jz_eq : jz = ∑ v, ((∑ i, (W v).w i) + n * m v)
  J : Subgroup (GLw n w₀)
  χ : J →* ℂˣ
  cusp : ∀ (σ : SmIrr (GLw n w₀)) (v : σ.V), v ≠ 0 → (∀ g : J, σ.ρ g v = ((χ g : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ
  tf : ∀ y ∈ J, ∀ k : ℕ, 0 < k → y ^ k = 1 → y = 1
  S : Finset (Plc E)
  Kw : ∀ w : Plc E, Subgroup (GLw n w)
  Φ : GUf E n → Module.Dual ℂ W.Sp
  κ : HChar E
  split : IsSplitAt w₀
  shape : Shape Up w₀ S Kw
  Kw0 : Kw w₀ = J
  ker_open : IsOpen {k : J | χ k = 1}
  opn : IsOpen (lev S Kw : Set (GUf E n))
  cpt : IsCompact (lev S Kw : Set (GUf E n))
  sph : ∀ w, IsSplitAt w → Apart w w₀ → (∃ B, SatU U w B) → w ∉ S ∧ CertificateRingHomMap.cj w ∉ S
  form : IsForm U W jz w₀ J χ S Kw Φ
  kap : IsKap x W jz S Φ κ

variable {x : E} {U : Submodule ℂ (UA E n → ℂ)} {w₀ : Plc E} {Up : Plc E → Prop} {S : Setup A n p}

def Vec.lam (V : Vec x U w₀ Up) (τ : E →+* ℂ) (i : Fin n) : ℕ :=
  if τ = (InfinitePlace.mk τ).embedding then V.m (InfinitePlace.mk τ) else ((V.W (InfinitePlace.mk τ)).w i + V.m (InfinitePlace.mk τ)).toNat

def Stab (F : Frame S) (V : Vec x U w₀ Up) (k : S.G.GAf) : Prop :=
  ∃ k', F.j k' = k ∧ F.th k' ∈ lev V.S V.Kw ∧ ∃ h : comp w₀ (F.th k') ∈ V.J, V.χ ⟨_, h⟩ = 1

def IsT (w : Plc E) (i : ℕ) (t : GLw n w) : Prop :=
  ∃ ϖ : w.adicCompletion E, Formalism.UG.IsUnifV E w ϖ ∧ t.val = Matrix.diagonal fun k : Fin n => if (k : ℕ) < i then ϖ else 1

def IsH (F : Frame S) (x : E) (w : Plc E) (i : ℕ) (h : S.G.GAf) : Prop :=
  ∃ (hw : IsSplitAt w) (t : GLw n w) (z : GUf E n), IsT w i t ∧ IsCen x w z ∧ h = F.j (loc hw t * z ^ i)

structure Site (S : Setup A n p) (N : Lv p) (w : Plc E) : Type where
  q : ℕ
  r : ℤ
  𝔞 : Ideal (𝓞 E)
  K₀ : Subgroup S.G.GAf
  good : A.Good q
  atp : AtPrime S.D q r w.asIdeal
  lv : LevAt S.D q r w.asIdeal (ordCompl[q] N.1) 𝔞
  isLev : IsLev S.L (Ideal.span {((ordCompl[q] N.1 : ℕ) : 𝓞 E)} * 𝔞) K₀
  mem : ((N.1 : ℕ) : 𝓞 E) ∈ Ideal.span {((ordCompl[q] N.1 : ℕ) : 𝓞 E)} * 𝔞

def Site.Compat {N : Lv p} {w w' : Plc E} (σ : Site S N w) (σ' : Site S N w') : Prop :=
  σ.q = σ'.q → σ.r = σ'.r ∧ σ.𝔞 = σ'.𝔞

def IsDeckM {N : Lv p} (g : Mem S.L N) : Prop := g.K = S.L.KN N.1 ∧ g.M = N ∧ g.h ∈ S.L.KN 1

def IsTM (F : Frame S) (x : E) {N : Lv p} {w : Plc E} (σ : Site S N w) (i : ℕ) (g : Mem S.L N) : Prop :=
  i ≤ n ∧ g.K = σ.K₀ ∧ IsH F x w i g.h ∧ g.M.1 = N.1 * Ideal.absNorm w.asIdeal ^ i

def idx {N : Lv p} (g : Mem S.L N) : ℕ := (S.L.KN g.M.1).relIndex (g.K ⊓ g.K.comap (MulAut.conj g.h).toMonoidHom)

def Free (V : Vec x U w₀ Up) (w : Plc E) : Prop :=
  IsSplitAt w ∧ w ∉ V.S ∧ CertificateRingHomMap.cj w ∉ V.S ∧ (∀ u ∈ V.S, ¬ SameK x (CertificateRingHomMap.cj u) w) ∧ ¬ SameK x (CertificateRingHomMap.cj w) w

def Seen (F : Frame S) (V : Vec x U w₀ Up) (r₀ : ℕ) {N : Lv p} (g : Mem S.L N) (θ : ℂ) : Prop :=
  (IsDeckM g ∧ Stab F V g.h ∧ g.h ∈ S.L.KN r₀ ∧ θ = 1) ∨
  ∃ (w : Plc E) (σ : Site S N w) (i : ℕ) (B : Multiset ℂˣ), Free V w ∧ σ.q ≠ r₀ ∧ (∀ k ∈ σ.K₀, Stab F V k) ∧ IsTM F x σ i g ∧ SatU U w B ∧
    θ = (idx g : ℂ) * (satEig (Ideal.absNorm w.asIdeal) n B i * (((V.κ.val w : ℂˣ) : ℂ)⁻¹) ^ i)

def Frame.cmp (F : Frame S) (w : Plc E) (g : GUf E n) : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (F.a w * comp w g * (F.a w)⁻¹).val

def InId (w : Plc E) (𝔟 : Ideal (𝓞 E)) (y : w.adicCompletion E) : Prop :=
  ∃ z ∈ 𝔟.map (algebraMap (𝓞 E) (w.adicCompletionIntegers E)), (z : w.adicCompletion E) = y

def Gen (A : Arith E) (x : E) : Prop := (A.ω : E) ∈ IntermediateField.adjoin ℚ {x} ∧ x ∈ IntermediateField.adjoin ℚ {(A.ω : E)}

def Off (V : Vec x U w₀ Up) (p : ℕ) : Prop :=
  (∀ u ∈ V.S, (p : 𝓞 E) ∉ u.asIdeal) ∧ ∃ g₀, V.Φ g₀ ≠ 0 ∧ ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w g₀ ∈ KGL w n

end UpperTheory.Gal.Int.Geo.Pl

namespace UpperTheory.Gal.Int.Geo.Pl

open GlobalTheory.CongL GlobalTheory.RoadWGeo Formalism.MainNotions.N Formalism.BasicNotions Formalism.ConjugateSelfDual
open UpperTheory.Gal.LocalSmoothExtension (Spec IsHExp conjWt epsOf)
attribute [local instance] Ideal.Quotient.field

def FrameEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p), Odd n → Nonempty (Frame S)

def VecEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n l d : ℕ), 0 < n → 0 < d → ∀ x : E, x ^ 2 = -(d : E) →
    ∀ U : Submodule ℂ (UA E n → ℂ), IsAutRepU U → ∀ w₀ : Plc E, IsSplitAt w₀ → GlobalTheory.CongW.TyEll E l n w₀ U →
    ∀ Up : Plc E → Prop, (∀ w, IsSplitAt w → Up w ∨ Up (CertificateRingHomMap.cj w)) → Up w₀ → Nonempty (Vec x U w₀ Up)

def SpecTop : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (F : Frame S)
    (x : E) (U : Submodule ℂ (UA E n → ℂ)) (w₀ : Plc E) (Up : Plc E → Prop) (V : Vec x U w₀ Up),
    Odd n → Sc S.D S.G → Gen A x → Off V p → (∃ q : ℕ, q.Prime ∧ A.Good q ∧ (q : 𝓞 E) ∈ w₀.asIdeal) → ∀ X : Finset ℕ, ∃ r₀ : ℕ, r₀.Prime ∧ r₀ ∉ X ∧ r₀ ≠ p ∧
      ∀ N : Lv p, r₀ ∣ N.1 → (∀ k ∈ S.L.KN N.1, Stab F V k) → ∀ (J : Type) (g : J → Mem S.L N) (θ : J → ℂ),
        (∀ j, Seen F V r₀ (g j) (θ j)) → ∃ f, IsFnL S.L N.1 f ∧ Spec S.L V.lam (S.L.KN N.1) (fun j => (g j).fn) θ f

def WtOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
    (x : E) (U : Submodule ℂ (UA E n → ℂ)) (w₀ : Plc E) (Up : Plc E → Prop) (V : Vec x U w₀ Up)
    (thQ : GL (Fin n) E × ℚˣ →* GL (Fin n) E × ℚˣ), (∀ y, (thQ y).1.val = (y.1⁻¹).valᵀ ∧ (thQ y).2 = y.2⁻¹) →
    LocalSmoothExtension.IsWt S.L V.lam ((CertificateRingHomMap.xi V.W V.jz).comp thQ)

def ExpOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
    (x : E) (U : Submodule ℂ (UA E n → ℂ)) (w₀ : Plc E) (Up : Plc E → Prop) (V : Vec x U w₀ Up),
    ∀ d : ℕ, 0 < d → x ^ 2 = -(d : E) → Gen A x →
    (∀ τ, Antitone (V.lam τ)) ∧ ∀ τ : E →+* ℂ, ∃ σ : ℂ ≃+* ℂ, (∀ y, σ (τ y) = A.τ₀ y) ∧
      ∀ lam, HasWeightAt U τ lam → ∀ j ∈ GlobalTheory.RoadWGeo.wtJumps lam, ∃ (h : Fin n → ℕ) (i : Fin n),
        IsHExp A.τ₀ (epsOf S.D) (conjWt σ V.lam) h ∧ (h i : ℤ) = j + mOf x V.W V.jz τ

def IntCof : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : GUf E n), ∀ᶠ w in Filter.cofinite, comp w g ∈ KGL w n

def PrimeProj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n q : ℕ), q.Prime → ∃ π : GUf E n →* GUf E n, ∀ (g : GUf E n) (w : Plc E),
    ((q : 𝓞 E) ∈ w.asIdeal → comp w (π g) = comp w g) ∧ ((q : 𝓞 E) ∉ w.asIdeal → comp w (π g) = 1)

def CenEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n d : ℕ) (x : E), 0 < d → x ^ 2 = -(d : E) → ∀ w : Plc E,
    ¬ SameK x (CertificateRingHomMap.cj w) w → (∀ q : ℕ, q.Prime → (q : 𝓞 E) ∈ w.asIdeal → ∀ u : Plc E, (q : 𝓞 E) ∈ u.asIdeal →
      SameK x u w ∨ SameK x (CertificateRingHomMap.cj u) w) → ∃ z : GUf E n, IsCen x w z

def Sides : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (x : E), Gen A x → ∀ q : ℕ, q.Prime → A.SplitK q →
    ∀ w : Plc E, (q : 𝓞 E) ∈ w.asIdeal → ¬ SameK x (CertificateRingHomMap.cj w) w ∧ IsSplitAt w ∧
      (∀ u : Plc E, (q : 𝓞 E) ∈ u.asIdeal → SameK x u w ∨ SameK x (CertificateRingHomMap.cj u) w) ∧ (∀ u : Plc E, SameK x u w → (q : 𝓞 E) ∈ u.asIdeal) ∧
      (∀ u u' : Plc E, SameK x u u' → SameK x (CertificateRingHomMap.cj u) (CertificateRingHomMap.cj u')) ∧
      (∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - A.tr * r + A.nm ∧ A.ω - (r : 𝓞 E) ∈ w.asIdeal) ∧
      ∀ r : ℤ, A.ω - (r : 𝓞 E) ∈ w.asIdeal → ∀ u : Plc E, SameK x u w ↔ (q : 𝓞 E) ∈ u.asIdeal ∧ A.ω - (r : 𝓞 E) ∈ u.asIdeal

def Dict : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (F : Frame S) (g : GUf E n),
    (Integ S.L (F.j g) ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i k, F.cmp w g i k ∈ w.adicCompletionIntegers E) ∧
    (F.j g ∈ S.L.KN 1 ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → F.a w * comp w g * (F.a w)⁻¹ ∈ KGL w n) ∧
    (∀ 𝔟 : Ideal (𝓞 E), 𝔟 ≠ ⊥ → (CongId S.L 𝔟 (F.j g) ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i k, InId w 𝔟 ((F.cmp w g - 1) i k))) ∧
    (∀ c : ℕ, (∀ v ∈ LaHat S.D, ∃ v' ∈ LaHat S.D, S.L.actG (F.j g) v' = c • v) ↔
      ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i k, (c : w.adicCompletion E) * F.cmp w g⁻¹ i k ∈ w.adicCompletionIntegers E)

def LevBasic : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G),
    (∀ 𝔟, ∃ K, IsLev L 𝔟 K) ∧ (∀ 𝔟 𝔟' K K', IsLev L 𝔟 K → IsLev L 𝔟' K' → 𝔟 ≤ 𝔟' → K ≤ K') ∧
    (∀ N : ℕ, IsLev L (Ideal.span {(N : 𝓞 D.F)}) (L.KN N)) ∧ (∀ (N : ℕ) g, L.CongOne N g ↔ CongId L (Ideal.span {(N : 𝓞 D.F)}) g) ∧
    (∀ 𝔟 K, IsLev L 𝔟 K → ∀ k ∈ L.KN 1, ∀ u ∈ K, k * u * k⁻¹ ∈ K) ∧
    ∀ (N c : ℕ) (h : G.GAf), Integ L h → (∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h v' = c • v) → 0 < c →
      ∀ u ∈ L.KN (N * c), h * u * h⁻¹ ∈ L.KN N

def TjOK : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (F : Frame S) (x : E), Gen A x →
    ∀ (N : Lv p) (w : Plc E) (σ : Site S N w) (i : ℕ), i ≤ n → ∀ h, IsH F x w i h → Integ S.L h ∧ IsTjElt S.L σ.q σ.r w.asIdeal i h

def TjIdx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (F : Frame S) (x : E), Gen A x →
    ∀ (N : Lv p) (w : Plc E) (σ : Site S N w) (i : ℕ), i ≤ n → ∀ h, IsH F x w i h → ∀ [w.asIdeal.IsMaximal],
      (σ.K₀ ⊓ σ.K₀.comap (MulAut.conj h).toMonoidHom).relIndex σ.K₀ =
        Nat.card (crystallineComparison.Gr (𝓞 E ⧸ w.asIdeal) (Fin n → 𝓞 E ⧸ w.asIdeal) i)

def MemEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (F : Frame S) (d : ℕ) (x : E), 0 < d → x ^ 2 = -(d : E) → Gen A x → ∀ N : Lv p,
    (∀ k ∈ S.L.KN 1, ∃ g : Mem S.L N, IsDeckM g ∧ g.h = k) ∧
    ∀ (w : Plc E) (σ : Site S N w) (i : ℕ), i ≤ n → ∃ g : Mem S.L N, IsTM F x σ i g

def SiteTriv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (x : E), Gen A x → ∀ (N : Lv p) (q : ℕ), q.Prime → q ≠ p → A.Good q → ¬ q ∣ N.1 →
    ∀ w : Plc E, (q : 𝓞 E) ∈ w.asIdeal → ∃ σ : Site S N w, σ.q = q ∧ σ.K₀ = S.L.KN N.1

def SiteEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (F : Frame S)
    (x : E) (U : Submodule ℂ (UA E n → ℂ)) (w₀ : Plc E) (Up : Plc E → Prop) (V : Vec x U w₀ Up),
    Gen A x → Off V p → ∀ (Q : Finset (Plc E)) (q : Plc E → ℕ),
    (∀ w ∈ Q, (q w).Prime ∧ q w ≠ p ∧ A.Good (q w) ∧ (q w : 𝓞 E) ∈ w.asIdeal ∧ Free V w ∧ ∀ w' ∈ Q, q w = q w' → SameK x w w') →
    ∀ c : ℕ, 0 < c → c.Coprime p → ∃ (N : Lv p) (σ : ∀ w ∈ Q, Site S N w), c ∣ N.1 ∧ (∀ k ∈ S.L.KN N.1, Stab F V k) ∧
      (∀ w hw, (q w) ∣ N.1 ∧ (σ w hw).q = q w ∧ ∀ k ∈ (σ w hw).K₀, Stab F V k) ∧ ∀ w hw w' hw', (σ w hw).Compat (σ w' hw')

def GoodOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (F : Frame S) (x : E), Gen A x →
    ∀ (N : Lv p) (v : Plc E) (σ : Site S N v) (J L : Type) [Field L] (g : J → Mem S.L N) (θ : J → L), Deck g θ σ.K₀ →
    (∀ j, IsDeckM (g j) ∨ ∃ (w : Plc E) (σ' : Site S N w) (i : ℕ), w ≠ v ∧ σ.Compat σ' ∧ IsTM F x σ' i (g j)) →
    GoodGrp g θ v.asIdeal

def CongOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (F : Frame S) (x : E), Gen A x →
    ∀ (N : Lv p) (w : Plc E) (σ : Site S N w) (J L : Type) [Field L] (g : J → Mem S.L N) (θ : J → L) (ϑ : ℕ → L), Deck g θ σ.K₀ →
    (∀ i ≤ n, ∃ j, IsTM F x σ i (g j) ∧ θ j = (idx (g j) : ℕ) * ϑ i) → CongGrp g θ w.asIdeal ϑ

def DatEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (n d : ℕ), Odd n → FieldOK E l d → ∀ x : E, x ^ 2 = -(d : E) →
    ∀ Q : Finset ℕ, (∀ q ∈ Q, ∃ _ : Fact q.Prime, IsSquare (-(d : ℚ_[q]))) →
    ∃ A : Arith E, 0 < d ∧ Gen A x ∧ (∀ q ∈ Q, A.Good q) ∧
      (∃ e : ℕ, 0 < e ∧ ∀ (q : ℕ) [Fact q.Prime], IsSquare (-(d : ℚ_[q])) → ¬ q ∣ e → A.Good q) ∧
      ∀ X : Finset ℕ, ∃ (p : ℕ) (_ : Fact p.Prime) (S : Setup A n p), p ∉ X ∧ Sc S.D S.G

end UpperTheory.Gal.Int.Geo.Pl
