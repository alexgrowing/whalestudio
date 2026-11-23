import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.SharpRestriction.GrowthBounds.ChartComparison

noncomputable section

namespace Formalism.L2.KerInert.SecondKernelProjection

open Formalism.MainNotions.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Classical

section Sel

variable {K A B : Type} [Field K] [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]

def projR (R : Submodule K (A × B)) : R →ₗ[K] R.map (LinearMap.fst K A B) :=
  LinearMap.codRestrict _ ((LinearMap.fst K A B).comp R.subtype) fun r => Submodule.mem_map.2 ⟨r.1, r.2, rfl⟩

theorem projR_surj (R : Submodule K (A × B)) : Function.Surjective (projR R) := by
  rintro ⟨a, ha⟩
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 ha
  exact ⟨⟨y, hy⟩, rfl⟩

def secR (R : Submodule K (A × B)) : R.map (LinearMap.fst K A B) →ₗ[K] B :=
  (LinearMap.snd K A B).comp (R.subtype.comp
    (Classical.choose (LinearMap.exists_rightInverse_of_surjective (projR R)
        (LinearMap.range_eq_top.2 (projR_surj R)))))

def selOf (R : Submodule K (A × B)) : A →ₗ[K] B :=
  Classical.choose (LinearMap.exists_extend (secR R))

end Sel

section Val

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {p : ℕ}
  (S : StepLevel F E σ J T f bad) (emb : Tau → E →+* ℂ) (G : GAtP p) (A : LocAt F E n G)
  (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
  {V cls : Type} [AddCommGroup V] [Module ℂ V] (embV : V →ₗ[ℂ] (cls → Frames (gramC J emb) → ℂ))
  (yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F))

def IsValV (x : V) (i : G.comp) (L : G.P.Tup) (Q : XR G.P ℂ) : Prop :=
  ∀ g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v),
    (∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) →
    ∀ (c : cls) (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
    A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (yc c).1 * κ.1) →
    ∀ z z' : Frames (gramC J emb), IsTr (atInf emb γ) z' z →
    evC G.P A.rk pos (gramC J emb) (crdB emb A.B) Q z = (S.chi κ : ℂ) * embV x c z'

def relV (i : G.comp) (L : G.P.Tup) : Submodule ℂ (V × XR G.P ℂ) where
  carrier := {q | IsValV S emb G A pos embV yc q.1 i L q.2}
  add_mem' := by
    intro a b ha hb g hg c γ hγ κ hp z z' hz
    have h1 := ha g hg c γ hγ κ hp z z' hz
    have h2 := hb g hg c γ hγ κ hp z z' hz
    simp only [Prod.fst_add, Prod.snd_add, map_add, Pi.add_apply] at h1 h2 ⊢
    rw [h1, h2, mul_add]
  zero_mem' := by
    intro g hg c γ hγ κ hp z z' hz
    simp only [Prod.fst_zero, Prod.snd_zero, map_zero, Pi.zero_apply, mul_zero]
  smul_mem' := by
    intro r a ha g hg c γ hγ κ hp z z' hz
    have h1 := ha g hg c γ hγ κ hp z z' hz
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [h1]
    ring

end Val

section Step

open Formalism.BasicNotions Formalism.MainNotions.G.CmpJ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def mapSL {R : Type} {Kc : Type} [CommRing Kc] (ι : ℂ →+* Kc) :
    MvPolynomial R ℂ →ₛₗ[ι] MvPolynomial R Kc where
  toFun := MvPolynomial.map ι
  map_add' := map_add _
  map_smul' a Q := Formalism.L2.G.Cmp.map_smul' ι a Q

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m}
  {G : GAtP p} (S : StepIn M i hi G)

def rawR (β : S.Ch) : (C.cls i → C.Y i → ℂ) →ₗ[ℂ] ({c // S.chOf c = β} → Fr D i hi → ℂ) where
  toFun φ := fun cl z => φ cl.1 (S.eY.symm z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def nrmR (β : S.Ch) : (C.cls i → C.Y i → ℂ) →ₗ[ℂ] ({c // S.chOf c = β} → Fr D i hi → ℂ) :=
  S.kTw β • ((nrm (S.tw β) (S.K β).y).toLinearMap ∘ₗ rawR S β)

def relS (β : S.Ch) (a : S.cmpt β) (L : G.P.Tup) : Submodule ℂ ((C.cls i → C.Y i → ℂ) × XR G.P ℂ) :=
  relV (S.K β).lev (embT D) (S.charts.gat β) (S.loc β) S.pos (nrmR S β) (S.K β).y a L

def rdS {Kc : Type} [Field Kc] (ι : ℂ →+* Kc) (c' : G.comp) (L : G.P.Tup) :
    (C.cls i → C.Y i → ℂ) →ₛₗ[ι] MvPolynomial (Var G.P) Kc :=
  if G.P.IsLatTup L then (mapSL ι).comp (selOf (relS S (S.eC.symm c').1 (S.eC.symm c').2 L)) else 0

end Step

section Cons

open Formalism.BasicNotions Formalism.MainNotions.G.CmpJ

variable {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

def trC {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (hC : C = C') (i : ℕ) :
    (C'.cls i → C'.Y i → ℂ) ≃ₗ[ℂ] (C.cls i → C.Y i → ℂ) := by
  subst hC
  exact LinearEquiv.refl ℂ _

def OnChain (I : CmpJIn Tw u μ w h Lv) : Prop := ∀ j (hj : j + 1 ≤ D.R.m), (I.at' j hj).C = D.chTw u μ

def IotaTie {Kf Kc : Type} [Field Kf] [Field Kc] [Algebra Kf Kc] (D : D7) (e : D.what₂.LL →+* Kf) (ι : ℂ →+* Kc) : Prop :=
  ∀ r : D.what₂.LL, ι (D.what₂.embLL r) = algebraMap Kf Kc (e r)

def rdJ (I : CmpJIn Tw u μ w h Lv) (hC : OnChain I) {Kc : Type} [Field Kc] (ι : ℂ →+* Kc) (j : ℕ) (c' : Lv.comp (j + 1))
    (L' : (Fl.Pj (j + 1)).Tup) :
    ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] Formalism.MainNotions.FormalGroupSystem.XspC (Fl.Pj (j + 1)) Kc :=
  if hj : j + 1 ≤ D.R.m then (rdS (I.at' j hj).st ι c' L').comp (trC (hC j hj) (j + 1)).toLinearMap else 0

end Cons

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances

def TieReadJ : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (K : KerLabelsMu ex.tw u μ w h Lv)
    (I : CmpJIn ex.tw u μ w h Lv) (H : CmpJHyp ex.cmp I) (hS : BlockRationalityField) (Gt : GatTies D) (hCh : _) (hC : OnChain I)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)) (ι : ℂ →+* Y.Kc),
    @IotaTie _ _ _ Y.fieldKc Y.algKf D (ex.cmp.embW u w h) ι → ∀ j : ℕ,
      TieReadAt (Y := Y) u μ (kerAtMu_any K H hS Gt Ch hCh).cmp ι (rdJ I hC ι) j

end Formalism.L2.KerInert.SecondKernelProjection
