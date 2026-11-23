import Formalism.LocalToGlobal.HermitianForms.LastCoordinateUniformizerVectorSpansOrthogonalLi
import Formalism.LocalToGlobal.HermitianForms.TransportT

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

def IsUkKg {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (gp : Fin 2 → ℕ) : Prop :=
  ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
    ∃ (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
      (fr : GL (Fin n) (v.adicCompletion F)),
      (∀ x, sp (sigR σ (v.adicCompletion F) x) = swapR _ (sp x)) ∧
      ∀ x ∈ UPts σ J (v.adicCompletion F),
        x ∈ S.Uloc v ↔ fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) x * fr ∈ iwU F n v

variable {D : D7}

def EvzTie {u : D.what₂.Word} {A : AtTTied u} {K : ClsPTied u} {P : LvTied u A D.R.m le_rfl}
    {Tl : TilTied u A K P} {Km : ClsTied u D.R.m le_rfl}
    (Ta : TilAd Tl Km) (W : ValTied u A.eV D.R.m le_rfl Km)
    (eWz : (D.mem u).P.Wz ≃ₗ[ℂ] ((D.fm u).clsP → (D.mem u).C.Y D.R.m → ℂ)) : Prop :=
  ∀ (φ : (D.mem u).C.cls D.R.m → (D.mem u).C.Y D.R.m → ℂ) c s s',
    IsTr (atInf (embT D) (Tl.ga c).1.1) (W.eY s') (W.eY s) →
    eWz ((D.mem u).P.evz φ) c s = (((Km.lev.chi (Ta.ka c))⁻¹ : ℂˣ) : ℂ) * φ ((D.fm u).til c) s'

open Classical in

def BwTie {u : D.what₂.Word} (A : AtTTied u) {i : ℕ} {hi : i ≤ D.R.m} {K : ClsTied u i hi}
    (W : ValTied u A.eV i hi K) : Prop :=
  ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → (D.fm u).seenP w = true →
    ∀ v (x : ((D.fm u).lat i).V), x ∈ (D.fm u).Bw i w v ↔
    ∀ (c : (D.mem u).C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E),
      IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B → IsLocBasis (D.mem u).A.T (Lk A i hi v c : Set _) B' →
      ∃ P ∈ IntSpan D w ((D.fm u).lam i), ∀ z, (D.fm u).emb i x c z =
        fnOf _ (shiftOf (lamT u i))
          (fun τ => if τ = (D.fm u).tauOf w v then atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 τ
            else atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 τ) P (W.eY z)

def PerTie (u : D.what₂.Word) (jM : (D.mem u).P.Mt →ₛₗ[starRingEnd ℂ] (D.mem u).P.Wrow) : Prop :=
  (∀ z ∈ (D.fm u).ptC, ∃ F, jM F = z) ∧ (∀ F, jM F ∈ (D.fm u).ptC) ∧
    ∀ w F, (D.mem u).P.period w F = (D.fm u).ipP (jM F) w

def subP {ι : Type} {n : ℕ} (o : ι → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (ι × Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ :=
  MvPolynomial.aeval fun x => ∑ a', MvPolynomial.C (o x.1 x.2.1 a') * MvPolynomial.X (x.1, a', x.2.2)

def embS (D : D7) (s : D.what₂.LL →+* ℂ) : D.what₂.Tau → D.host.E →+* ℂ :=
  fun τ => s.comp (D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E))

def NormTie {u : D.what₂.Word} {eV : (D.mem u).A.vT ≃ PlT D u} {i : ℕ} {hi : i ≤ D.R.m} {K : ClsTied u i hi}
    (W : ValTied u eV i hi K) : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ) (x : ((D.fm u).lat i).V)
    (Pc : (D.mem u).C.cls i → MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) D.what₂.LL),
    (∀ c z, (D.fm u).emb i x c z =
      fnOf _ (shiftOf (lamT u i)) 1 (MvPolynomial.map D.what₂.embLL (Pc c)) (W.eY z)) →
    ∀ o : Frames (gramC (gramN D i hi) (embS D s)), o.IsON →
      (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat i).b ((D.fm u).lat i).X (InfinitePlace.mk s) x x).re =
        ∑ c, ((D.mem u).C.wt i c).re * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (lamT u i) τ)) *
          (nfAll ((D.fm u).lam i) (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re

def NormPTie {u : D.what₂.Word} {K : ClsPTied u} (W : ValPTied u K) : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ) (x : (D.fm u).ptLat.V)
    (Pc : (D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) D.what₂.LL),
    (∀ c, W.eW ((D.fm u).ptEmb x) c =
      fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))) →
    ∀ o : Frames (gramC (gramP D) (embS D s)), o.IsON →
      (Formalism.HermitianLatticesTheory.majAt (D.fm u).ptLat.b (D.fm u).ptLat.X (InfinitePlace.mk s) x x).re =
        ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℝ)⁻¹ * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
          (nfAll (D.fm u).sg (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re

def aOf (R : Ranks) (i : ℕ) : ℕ := if i < R.m then R.k + i else R.r

def skipOf (R : Ranks) (i : ℕ) : ℕ := if i + 1 < R.m then R.k else R.N i

def fcOf (R : Ranks) (i : ℕ) : ℕ := if R.m ≤ i + 1 then R.k else R.N i

theorem fcOf_lt {R : Ranks} {i : ℕ} (h : i + 1 < R.m) : fcOf R i = R.N i := if_neg (Nat.not_le.2 h)

theorem fcOf_ge {R : Ranks} {i : ℕ} (h : R.m ≤ i + 1) : fcOf R i = R.k := if_pos h

set_option maxHeartbeats 1000000 in

structure FormsTied (D : D7) (u : D.what₂.Word) where
  atT : AtTTied u
  cls : ∀ i hi, ClsTied u i hi
  val : ∀ i hi, ValTied u atT.eV i hi (cls i hi)

  gl : GLoc D.host.F D.host.E (sigD D) D.host.g
  gl_K : ∀ i, (gl.piG i : D.host.E) ∈ D.host.K

  glev : ∀ i hi, GLev (cls i hi).lev gl (aOf D.R i) D.R.t i (skipOf D.R i) (fcOf D.R i) (decide (i = D.R.m))
  lv : ∀ i hi, LvTied u atT i hi
  fMe : ∀ i hi v, (cls i hi).lev.fM (atT.eV v).1 (atT.eV v).2 ≃+ (D.mem u).A.Fv v
  fv : ∀ i hi, FvTie (lv i hi) (cls i hi) (fMe i hi)

  upN : ∀ i hi, UpNatTie (lv i hi) (cls i hi) (val i hi)
  dnN : ∀ i hi, DnNatTie (lv i hi) (cls i hi) (val i hi)
  norm : ∀ i hi, NormTie (val i hi)
  bw : ∀ i hi, BwTie atT (val i hi)
  clsP : ClsPTied u
  valP : ValPTied u clsP
  normP : NormPTie valP

  glevP : GLev clsP.lev gl D.R.r D.R.t D.R.m (D.R.N D.R.m) (fcOf D.R D.R.m) false
  til : TilTied u atT clsP (lv D.R.m le_rfl)
  tilLat : TilBaseLat til (cls D.R.m le_rfl)
  tilFv : TilBaseFv til (cls D.R.m le_rfl) (fMe D.R.m le_rfl)
  tilAd : TilAd til (cls D.R.m le_rfl)
  frExt : FrExt til.z0 (glev D.R.m le_rfl) glevP
  eWz : (D.mem u).P.Wz ≃ₗ[ℂ] ((D.fm u).clsP → (D.mem u).C.Y D.R.m → ℂ)
  evz : EvzTie tilAd (val D.R.m le_rfl) eWz
  jM : (D.mem u).P.Mt →ₛₗ[starRingEnd ℂ] (D.mem u).P.Wrow
  per : PerTie u jM

  DGam : (D.mem u).C.DGam = (D.mem D.u₀).C.DGam

theorem FormsTied.up {u : D.what₂.Word} (T : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) :
    UpTie (T.lv i hi) (T.cls i hi) (T.val i hi) := (T.upN i hi).upTie

theorem FormsTied.dn {u : D.what₂.Word} (T : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) :
    DnTie (T.lv i hi) (T.cls i hi) (T.val i hi) := (T.dnN i hi).dnTie

theorem Mu0_iff {u : D.what₂.Word} {eV : (D.mem u).A.vT ≃ PlT D u} {K : ClsTied u 0 (Nat.zero_le _)}
    (W : ValTied u eV 0 (Nat.zero_le _) K) (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) :
    φ ∈ (D.mem u).A.Mu0 ↔
      (fun c z => φ c (W.eY.symm z)) ∈ FiC K.lev (embT D) ((D.fm u).lam 0) K.y := by
  rw [← (D.fm u).Fi_zero, ← lamT_zero]; exact W.Fi φ

theorem rhoT_eq {u : D.what₂.Word} {eV : (D.mem u).A.vT ≃ PlT D u} {K : ClsTied u 0 (Nat.zero_le _)}
    (W : ValTied u eV 0 (Nat.zero_le _) K) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ)
    (hk : (k : (D.mem u).A.Fv v) = a) (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia K.lev (eV v).1 (eV v).2 k δ) (g) (hg : g ∈ AdFun K.lev (embT D)) :
    (D.mem u).A.rhoT v a (fun c s => g (K.y c) (W.eY s)) = fun c s => g (K.y c * δ) (W.eY s) := by
  funext c
  rw [(D.fm u).rhoT_dil]
  exact W.dilT v a k hk c δ hδ g hg

end Formalism.L2.Forms
