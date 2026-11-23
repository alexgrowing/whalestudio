import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsEtaleFirstChernUntwisted
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris GroundTheory.PAdicHodge Formalism.Per6

universe w w' v u v' u'

namespace CrystallineSemistableComparison.HT

open CH PAlg

section Gen
variable {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} {σ : R →+* R'}

def subMor (m : Mor F F' σ) (S : SubF F) (S' : SubF F') (h : ∀ T x, x ∈ S.S (m.G.obj T) → m.τ T x ∈ S'.S T) : Mor S.fn S'.fn σ where
  G := m.G
  τ T := { toFun := fun x => ⟨m.τ T (show S.S _ from x).1, h T _ (show S.S _ from x).2⟩
           map_add' := fun x y => Subtype.ext (map_add (m.τ T) _ _)
           map_smul' := fun r x => Subtype.ext (LinearMap.map_smulₛₗ (m.τ T) _ _) }
  nat φ x := Subtype.ext (m.nat φ _)

def mulTo (c : R) (S : SubF F) (h : ∀ (T : C) (x : F.obj T), c • x ∈ S.S T) : Mor F S.fn (RingHom.id R) where
  G := 𝟭 C
  τ T := { toFun := fun x => ⟨c • x, h T x⟩
           map_add' := fun x y => Subtype.ext (smul_add _ _ _)
           map_smul' := fun r x => Subtype.ext (smul_comm _ _ _) }
  nat φ x := Subtype.ext (map_smul (F.map φ).hom c x).symm

def mulSub (c : R) (S S' : SubF F) (h : ∀ (T : C) (x : F.obj T), x ∈ S.S T → c • x ∈ S'.S T) : Mor S.fn S'.fn (RingHom.id R) where
  G := 𝟭 C
  τ T := { toFun := fun x => ⟨c • (show S.S _ from x).1, h T _ (show S.S _ from x).2⟩
           map_add' := fun x y => Subtype.ext (smul_add _ _ _)
           map_smul' := fun r x => Subtype.ext (smul_comm _ _ _) }
  nat φ x := Subtype.ext (map_smul (F.map φ).hom c _).symm

def subPair {A : C ⥤ CommAlgCat.{w} R} (S S' S'' : SubF (modF A))
    (h : ∀ (T : C) (x y : A.obj T), x ∈ S.S T → y ∈ S'.S T → x * y ∈ S''.S T) : Pairing S.fn S'.fn S''.fn where
  μ T := LinearMap.mk₂ R (fun (x : S.S T) (y : S'.S T) => (⟨(show A.obj T from x.1) * (show A.obj T from y.1), h T _ _ x.2 y.2⟩ : S''.S T))
    (fun _ _ _ => Subtype.ext (add_mul (R := A.obj T) _ _ _)) (fun r x y => Subtype.ext (smul_mul_assoc (β := A.obj T) r _ _))
    (fun _ _ _ => Subtype.ext (mul_add (R := A.obj T) _ _ _)) (fun r x y => Subtype.ext (mul_smul_comm (β := A.obj T) r _ _))
  nat φ x y := Subtype.ext (map_mul (A.map φ).hom _ _).symm

end Gen

theorem pow_mem_pdP {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {z : B} (hz : z ∈ J) (k : ℕ) : z ^ k ∈ Pb.pdP δ k := by
  induction k with
  | zero => exact Ideal.subset_span ⟨[], by simp, by simp, by simp⟩
  | succ k ih =>
    rw [pow_succ]
    exact dividedPowerFiltration_mul δ k 1 ih (Ideal.subset_span ⟨[(1, z)], by simpa using hz, by simp, by simp [δ.dpow_one hz]⟩)

theorem dividedPowerFiltration_pow_mul {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {z x : B} (hz : z ∈ J) {r k r' : ℕ} (h : r + k = r')
    (hx : x ∈ Pb.pdP δ r) : z ^ k * x ∈ Pb.pdP δ r' := by
  rw [mul_comm, ← h]; exact dividedPowerFiltration_mul δ r k hx (pow_mem_pdP δ hz k)

section Pd
variable {b : Base} (L : b.Fun) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R)

def pdOm {L : b.Fun} {c : Λ →+* b.R} {b' : Base} {L' : b'.Fun} {σ : b.R →+* b'.R} (m : GlobalTheory.LogCris.Mor L L' σ) {Λ' : Type} [CommRing Λ']
    {c' : Λ' →+* b'.R} (σ₀ : Λ →+* Λ') (h : ∀ a, σ (c a) = c' (σ₀ a)) (r : ℕ) : CH.Mor (B.pdS L c r).fn (B.pdS L' c' r).fn σ₀ :=
  subMor (B.omMor m σ₀ h) (B.pdS L c r) (B.pdS L' c' r) fun _ _ hx => hx

def pdPair {r r' s : ℕ} (h : r + r' = s) : Pairing (B.pdS L c r).fn (B.pdS L c r').fn (B.pdS L c s).fn :=
  subPair (A := B.OA L c) (B.pdS L c r) (B.pdS L c r') (B.pdS L c s) fun T _ _ hx hy => h ▸ dividedPowerFiltration_mul T.δ r r' hx hy

def pdOne : H (B.pdS L c 0).fn 0 :=
  (mulTo 1 (B.pdS L c 0) fun T x => show (_ : T.B) ∈ T.pdPow 0 from T.pdPow_zero ▸ trivial).pull 0 (CH.oneH (B.OA L c))

def pdSh {t : Λ} (ht : c t ∈ b.I) {r r' : ℕ} (k : ℕ) (h : r + k = r') : CH.Mor (B.pdS L c r).fn (B.pdS L c r').fn (RingHom.id Λ) :=
  mulSub (t ^ k) (B.pdS L c r) (B.pdS L c r') fun T x hx => by
    have := dividedPowerFiltration_pow_mul T.δ (T.i_mem ht) h hx
    rw [← map_pow, ← map_pow] at this
    exact this

end Pd

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

variable (l) in

def TFil : Prop := ∀ (A : PAlg l) (n : ℕ), A.cris n (tA l) ∈ B.JJ false A n

def TT (P : PAlg l ⥤ Type) (r n : ℕ) : SubF (modF (AcrEl P n)) where
  S T := { carrier := {x | (show T.1.obj.Acr n from x) ∈ Pb.pdP (B.DD false T.1.obj n) r}
           add_mem' := fun hx hy => (Pb.pdP (B.DD false T.1.obj n) r).add_mem hx hy
           zero_mem' := (Pb.pdP (B.DD false T.1.obj n) r).zero_mem
           smul_mem' := fun a _ hx => (Pb.pdP (B.DD false T.1.obj n) r).mul_mem_left (T.1.obj.cris n a) hx }
  map_mem φ _ hx := Pb.dividedPowerFiltration_map (B.dd_map false φ.1.hom n) r hx

theorem mem_TT {P : PAlg l ⥤ Type} {r n : ℕ} {T : El P} {x : T.1.obj.Acr n} :
    x ∈ (TT P r n).S T ↔ x ∈ Pb.pdP (B.DD false T.1.obj n) r := Iff.rfl

theorem mem_pdS {b : Base} {L : b.Fun} {Λ : Type} [CommRing Λ] {c : Λ →+* b.R} {r : ℕ} {T : Thick L} {x : T.B} :
    x ∈ (B.pdS L c r).S T ↔ x ∈ Pb.pdP T.δ r := Iff.rfl

def βMorF {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l) (r n : ℕ) :
    CH.Mor (B.pdS (B.Lc F κ false n) ((base l).cris n) r).fn (TT (F.pt κ) r n).fn (RingHom.id _) :=
  subMor (B.βMor F κ false n) _ _ fun T x hx =>
    mem_TT.2 ((mem_pdS (T := B.gObj F κ false n ((B.jE _).obj T))).1 hx)

def tMor (ht : TFil l) (P : PAlg l ⥤ Type) (r n : ℕ) : CH.Mor (modF (AcrEl P n)) (TT P r n).fn (RingHom.id _) :=
  mulTo (tA l ^ r) (TT P r n) fun T (x : T.1.obj.Acr n) => mem_TT.2 (by
    have := Ideal.mul_mem_right x _ (pow_mem_pdP (B.DD false T.1.obj n) (ht T.1.obj n) r)
    rw [← map_pow] at this
    exact this)

abbrev SS (M : Model l K) (r n : ℕ) : SubF (B.OM (M.L false n) ((base l).cris n)) := B.pdS (M.L false n) ((base l).cris n) r

abbrev SH (M : Model l K) (r n j : ℕ) : Type 1 := H (SS M r n).fn j

def Fam (M : Model l K) (r j : ℕ) : Type 1 := ∀ n, SH M r n j

instance (M : Model l K) (r j : ℕ) : AddCommGroup (Fam M r j) := Pi.addCommGroup
instance (M : Model l K) (r j : ℕ) : Module (Acris l) (Fam M r j) := Pi.module _ _ _

def redS (M : Model l K) (r n j : ℕ) : SH M r (n + 1) j →ₗ[Acris l] SH M r n j :=
  (pdOm (CrystallineSemistableComparison.SH.redM (B.schFn M.p) (okToOC l K) false n) (RingHom.id _) (B.red_cris _ n.le_succ) r).pull j

def Comp {M : Model l K} {r j : ℕ} (x : Fam M r j) : Prop := ∀ n, redS M r n j (x (n + 1)) = x n

def galS {M : Model l K} {r j : ℕ} (σ : K.fixingSubgroup) (x : Fam M r j) : Fam M r j := fun n =>
  (pdOm (CrystallineSemistableComparison.SH.galM (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _) false n)
    (ACris.galCris (IntermediateField.fixingSubgroupEquiv K σ)) (galBase_cris _ n) r).pull j (x n)

def pullS {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) {r j : ℕ} (x : Fam N r j) : Fam M r j := fun n =>
  (pdOm (CrystallineSemistableComparison.SH.pullM (okToOC l K) (B.schMap u hu) false n) (RingHom.id _) (CrystallineSemistableComparison.SH.idc _) r).pull j (x n)

def cupS {M : Model l K} {r r' s i j : ℕ} (h : r + r' = s) (x : Fam M r i) (y : Fam M r' j) : Fam M s (i + j) := fun n =>
  (pdPair (M.L false n) ((base l).cris n) h).cup rfl (x n) (y n)

def oneS (M : Model l K) : Fam M 0 0 := fun n => pdOne (M.L false n) ((base l).cris n)

variable (ht : TFil l)

def shS {M : Model l K} {r r' j : ℕ} (k : ℕ) (h : r + k = r') (x : Fam M r j) : Fam M r' j := fun n =>
  (pdSh (M.L false n) ((base l).cris n) (ht (base l) n) k h).pull j (x n)

def IsFirstChernClassInFamily {M : Model l K} (D : E.LineData M.X) (x : Fam M 1 2) : Prop :=
  ∀ (n : ℕ) (C : Type 1) [Category.{0} C] (G : C ⥤ Thick (M.L false n))
    (Λ : B.CLift (q := M.p) (b := B.bs l false n) (ht := rfl) (κ := B.κb (okToOC l K) false n) G D),
    ∃ (z : Cn (G ⋙ (SS M 1 n).fn) 2) (hz : d _ 2 z = 0),
      (∀ s, (show (SS M 1 n).S _ from z s).1 = Λ.coc ((base l).cris n) (l * n) s) ∧
      (cx _).cls z hz = (Mor.restrict (SS M 1 n).fn G).pull 2 (x n)

def IsLift (e : E.EtFam l K) {M : Model l K} (r : ℕ) {j : ℕ} (v : M.T j) (x : Fam M r j) : Prop :=
  Comp x ∧ ∀ n, (βMorF (B.schFn M.p) (okToOC l K) r n).pull j (x n) =
    (tMor ht ((B.schFn M.p).pt (okToOC l K)) r n).pull j (e M n j (v.lev n))

variable (l) in

def zA : ℤ_[l] →+* Acris l := (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l)).comp (IsPerfectoidField.padicIntToWitt l)

variable (l) in

def θA : Acris l →+* ℂ_[l] := (θD l).comp (ACris.iota ℂ_[l] l)

structure Half1 (Lf : ∀ {M : Model l K} (r : ℕ) {j : ℕ}, M.T j → Fam M r j → Prop) : Prop where
  comp : ∀ {M : Model l K} {r j : ℕ} {v : M.T j} {x : Fam M r j}, Lf r v x → Comp x
  ex : ∀ M : Model l K, M.Sm → ∀ j, ∃ r, ∀ v : M.T j, ∃ x, Lf r v x
  uniq : ∀ M : Model l K, M.Sm → ∀ j, ∃ k, ∀ (r : ℕ) (v : M.T j) (x x' : Fam M r j), Lf r v x → Lf r v x' →
    shS ht k rfl x = shS ht k rfl x'
  add : ∀ {M : Model l K} {r j : ℕ} {v v' : M.T j} {x x' : Fam M r j}, Lf r v x → Lf r v' x' → Lf r (v + v') (x + x')
  smul : ∀ {M : Model l K} {r j : ℕ} {v : M.T j} {x : Fam M r j} (z : ℤ_[l]), Lf r v x → Lf r (z • v) (zA l z • x)
  sh : ∀ {M : Model l K} {r r' j : ℕ} {v : M.T j} {x : Fam M r j} (k : ℕ) (h : r + k = r'), Lf r v x → Lf r' v (shS ht k h x)
  gal : ∀ {M : Model l K} {r j : ℕ} {v : M.T j} {x : Fam M r j} (σ : K.fixingSubgroup), Lf r v x →
    Lf r (DeRhamTwist.Twist.chi0 l σ.1 ^ r • M.actT j σ v) (galS σ x)
  nat : ∀ {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) {r j : ℕ} {v : N.T j} {x : Fam N r j}, Lf r v x →
    Lf r (Model.pullT u hu j v) (pullS u hu x)
  cup : ∀ {M : Model l K} {r r' s i j : ℕ} (h : r + r' = s) {v : M.T i} {v' : M.T j} {w : M.T (i + j)} {x : Fam M r i}
    {x' : Fam M r' j}, M.CupT v v' w → Lf r v x → Lf r' v' x' → Lf s w (cupS h x x')
  one : ∀ (M : Model l K) (v : M.T 0), (∀ k, v.lev k = GlobalTheory.EtC.one (l ^ k) M.spc) → Lf 0 v (oneS M)
  first_chern_class_exists : ∀ (M : Model l K) (D : E.LineData M.X) (r : E.Roots l), ∃ v, IsEtaleFirstChernUntwisted r D v
  c1 : ∀ (M : Model l K) (D : E.LineData M.X), Etale D.f → sSup (Pb.𝒱D D) = ⊤ → ∀ (r : E.Roots l) (v : M.T 2), IsEtaleFirstChernUntwisted r D v →
    ∃ x, IsFirstChernClassInFamily D x ∧ Lf 1 v x

set_option maxHeartbeats 1000000 in

structure Half2 (γ : ∀ {M : Model l K} {r j : ℕ}, Fam M r j → ∀ a, Module.Dual K (Hdg M.q a j) →+ ℂ_[l]) : Prop where
  add : ∀ {M : Model l K}, M.Sm → ∀ {r j : ℕ} (x y : Fam M r j), Comp x → Comp y → ∀ a, γ (x + y) a = γ x a + γ y a
  lin : ∀ {M : Model l K}, M.Sm → ∀ {r j : ℕ} (c : Acris l) (x : Fam M r j), Comp x → ∀ a φ, γ (c • x) a φ = θA l c * γ x a φ
  lin' : ∀ {M : Model l K}, M.Sm → ∀ {r j : ℕ} (x : Fam M r j), Comp x → ∀ a (k : K) φ, γ x a (k • φ) = kC K k * γ x a φ
  sh : ∀ {M : Model l K}, M.Sm → ∀ {r r' j : ℕ} (k : ℕ) (h : r + k = r') (x : Fam M r j), Comp x → ∀ a, γ (shS ht k h x) a = γ x a
  gal : ∀ {M : Model l K}, M.Sm → ∀ {r j : ℕ} (σ : K.fixingSubgroup) (x : Fam M r j), Comp x → ∀ a φ,
    qC l (period_ring_base.χ σ.1) ^ a * γ (galS σ x) a φ = qC l (period_ring_base.χ σ.1) ^ r * period_ring_base.σC σ.1 (γ x a φ)
  nat : ∀ {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p), M.Sm → N.Sm → ∀ {r j : ℕ} (x : Fam N r j), Comp x → ∀ a φ,
    γ (pullS u hu x) a φ = γ x a (φ ∘ₗ pullH (Model.genMap u hu) (Model.genMap_q u hu) a j)
  cup : ∀ {M : Model l K}, M.Sm → ∀ {r r' s i j : ℕ} (h : r + r' = s) (x : Fam M r i) (y : Fam M r' j), Comp x → Comp y →
    ∀ {m m' : ℕ → ℕ} (b : ∀ a, Module.Basis (Fin (m a)) K (Hdg M.q a i)) (b' : ∀ a, Module.Basis (Fin (m' a)) K (Hdg M.q a j))
      (c : ℕ) (φ : Module.Dual K (Hdg M.q c (i + j))),
      γ (cupS h x y) c φ = ∑ p : (Finset.HasAntidiagonal.antidiagonal c : Finset (ℕ × ℕ)), ∑ s, ∑ s',
        γ x p.1.1 ((b p.1.1).coord s) * γ y p.1.2 ((b' p.1.2).coord s') *
          kC K (φ (cupH M.q (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2) rfl (b p.1.1 s) (b' p.1.2 s')))
  one : ∀ {M : Model l K}, M.Sm → ∀ φ, γ (oneS M) 0 φ = kC K (φ (oneH M.q))
  c1 : ∀ {M : Model l K}, M.Sm → ∀ (D : E.LineData M.X), sSup (Pb.𝒱D D) = ⊤ → ∀ (x : Fam M 1 2) (c : Hdg M.q 1 2),
    Comp x → IsFirstChernClassInFamily D x → IsDlogFirstChernClass M.q (genD D) c → (∀ φ, γ x 1 φ = kC K (φ c)) ∧ ∀ a, a ≠ 1 → γ x a = 0

end CrystallineSemistableComparison.HT
