import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.Columns.AtTLemmas

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Abs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure Nbr (S : GSD K) where
  up : S.D → Finset S.D
  dn : S.D → Finset S.D
  mem_iff : ∀ d d' : S.D, d' ∈ up d ↔ d ∈ dn d'
  equiv : ∀ (g : S.G) (d d' : S.D), g • d' ∈ up (g • d) ↔ d' ∈ up d

variable {S : GSD K}

def Nbr.U (n : Nbr S) : Module.End K S.EqFun :=
  (LocOp.ofNbr (S := S) (S' := S) (MonoidHom.id _) n.up LinearMap.id (fun g d' d => n.equiv g d' d) (fun _ _ => rfl)).op

theorem Nbr.sum_up_smul (n : Nbr S) {M : Type} [AddCommMonoid M] (g : S.G) (d : S.D) (F : S.D → M) :
    ∑ d' ∈ n.up (g • d), F d' = ∑ d' ∈ n.up d, F (g • d') := by
  refine Finset.sum_nbij' (fun x => g⁻¹ • x) (fun x => g • x) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [← n.equiv g, smul_inv_smul]
    exact hx
  · intro x hx
    exact (n.equiv g d x).2 hx
  · intro x _
    exact smul_inv_smul g x
  · intro x _
    exact inv_smul_smul g x
  · intro x _
    rw [smul_inv_smul]

def CplFun (Y : Cpl S) : Submodule K (S.D → Y.Yb → S.V) where
  carrier := {G | ∀ (g : S.G) (d : S.D) (y : Y.Yb), G (g • d) (g • y) = S.ρ g (G d y)}
  add_mem' := fun {G G'} h h' g d y => by
    show G (g • d) (g • y) + G' (g • d) (g • y) = S.ρ g (G d y + G' d y)
    rw [h, h', map_add]
  zero_mem' := fun g _ _ => (map_zero (S.ρ g)).symm
  smul_mem' := fun a G h g d y => by
    show a • G (g • d) (g • y) = S.ρ g (a • G d y)
    rw [h, map_smul]

def Nbr.UYfun (n : Nbr S) (Yb : Type) : Module.End K (S.D → Yb → S.V) where
  toFun G := fun d y => ∑ d' ∈ n.up d, G d' y
  map_add' G G' := by
    funext d y
    exact Finset.sum_add_distrib
  map_smul' a G := by
    funext d y
    show ∑ d' ∈ n.up d, a • G d' y = a • ∑ d' ∈ n.up d, G d' y
    rw [Finset.smul_sum]

theorem Nbr.UYfun_mem (n : Nbr S) (Y : Cpl S) {G : S.D → Y.Yb → S.V} (hG : G ∈ CplFun Y) : n.UYfun Y.Yb G ∈ CplFun Y := by
  intro g d y
  show ∑ d' ∈ n.up (g • d), G d' (g • y) = S.ρ g (∑ d' ∈ n.up d, G d' y)
  rw [n.sum_up_smul, map_sum]
  exact Finset.sum_congr rfl fun d' _ => hG g d' y

def Nbr.UY (n : Nbr S) (Y : Cpl S) : Module.End K (CplFun Y) :=
  (n.UYfun Y.Yb).restrict fun _ h => n.UYfun_mem Y h

def cp1Op {S₀ : GSD K} {Y : Cpl S} (k1 : S₀.D → S.D → Y.Yb → (S₀.V →ₗ[K] S.V))
    (he1 : ∀ (g₀ : S₀.G) (g : S.G) (d₀ : S₀.D) (d : S.D) (y : Y.Yb), k1 (g₀ • d₀) (g • d) (g • y) = (S.ρ g) ∘ₗ (k1 d₀ d y) ∘ₗ (S₀.ρ g₀⁻¹))
    (h₀ : S₀.Ok) (s₀ : S₀.Sec) : S₀.EqFun →ₗ[K] CplFun Y where
  toFun φ := ⟨fun d y => S₀.csOf h₀ s₀ fun d₀ => k1 d₀ d y ((φ : S₀.D → S₀.V) d₀), fun g d y => by
    unfold GSD.csOf
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h1 := he1 1 g (s₀.rep c) d y
    rw [one_smul, inv_one, map_one] at h1
    beta_reduce
    rw [h1, map_smul]
    rfl⟩
  map_add' φ ψ := by
    apply Subtype.ext
    funext d y
    show S₀.csOf h₀ s₀ (fun d₀ => k1 d₀ d y ((φ : S₀.D → S₀.V) d₀ + (ψ : S₀.D → S₀.V) d₀)) =
      S₀.csOf h₀ s₀ (fun d₀ => k1 d₀ d y ((φ : S₀.D → S₀.V) d₀)) + S₀.csOf h₀ s₀ (fun d₀ => k1 d₀ d y ((ψ : S₀.D → S₀.V) d₀))
    unfold GSD.csOf
    simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' a φ := by
    apply Subtype.ext
    funext d y
    show S₀.csOf h₀ s₀ (fun d₀ => k1 d₀ d y (a • (φ : S₀.D → S₀.V) d₀)) = a • S₀.csOf h₀ s₀ (fun d₀ => k1 d₀ d y ((φ : S₀.D → S₀.V) d₀))
    unfold GSD.csOf
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    beta_reduce
    rw [map_smul, smul_comm]

def cp2Fun (Y : Cpl S) {D₁ V₁ : Type} [AddCommGroup V₁] [Module K V₁] (k2 : S.D → Y.Yb → D₁ → (S.V →ₗ[K] V₁)) (h : S.Ok) (s : S.Sec) :
    CplFun Y →ₗ[K] (D₁ → V₁) where
  toFun G := fun e => S.csOf h s fun d => ∑ y ∈ (Y.fin d).toFinset, k2 d y e ((G : S.D → Y.Yb → S.V) d y)
  map_add' G G' := by
    funext e
    show S.csOf h s (fun d => ∑ y ∈ (Y.fin d).toFinset, k2 d y e ((G : S.D → Y.Yb → S.V) d y + (G' : S.D → Y.Yb → S.V) d y)) =
      S.csOf h s (fun d => ∑ y ∈ (Y.fin d).toFinset, k2 d y e ((G : S.D → Y.Yb → S.V) d y)) +
        S.csOf h s (fun d => ∑ y ∈ (Y.fin d).toFinset, k2 d y e ((G' : S.D → Y.Yb → S.V) d y))
    unfold GSD.csOf
    simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' a G := by
    funext e
    show S.csOf h s (fun d => ∑ y ∈ (Y.fin d).toFinset, k2 d y e (a • (G : S.D → Y.Yb → S.V) d y)) =
      a • S.csOf h s (fun d => ∑ y ∈ (Y.fin d).toFinset, k2 d y e ((G : S.D → Y.Yb → S.V) d y))
    unfold GSD.csOf
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    beta_reduce
    simp only [map_smul]
    rw [← Finset.smul_sum, smul_comm]

def upFun (K : Type) [Field K] {D₁ : Type} (V₁ : Type) [AddCommGroup V₁] [Module K V₁] (up : D₁ → Finset D₁) : Module.End K (D₁ → V₁) where
  toFun F := fun e => ∑ e' ∈ up e, F e'
  map_add' F F' := by
    funext e
    exact Finset.sum_add_distrib
  map_smul' a F := by
    funext e
    show ∑ e' ∈ up e, a • F e' = a • ∑ e' ∈ up e, F e'
    rw [Finset.smul_sum]

def famU {F : GFam K} (n : ∀ b, Nbr (F.mem b)) : Module.End K F.Forms :=
  LinearMap.pi fun b => (n b).U ∘ₗ LinearMap.proj b

def CommC {V V' : Type} [AddCommMonoid V] [Module K V] [AddCommMonoid V'] [Module K V'] (U' : Module.End K V') (k : V →ₗ[K] V')
    (U : Module.End K V) (c : K) : Prop :=
  U' ∘ₗ k = c • (k ∘ₗ U)

def CommF {F F' : GFam K} (U' : Module.End K F'.Forms) (k : F.Forms →ₗ[K] F'.Forms) (U : Module.End K F.Forms) (c : K) : Prop :=
  CommC U' k U c

def Incl3 {S' : GSD K} (w : HeightOneSpectrum (𝓞 K)) (t : K) (U : Module.End K S'.EqFun) (k : S.EqFun →ₗ[K] S'.EqFun) : Prop :=
  ∀ φ ∈ atW w S.intDel, t • U (k φ) ∈ atW w S'.intDel

def CplInt (Y : Cpl S) (w : HeightOneSpectrum (𝓞 K)) (G : CplFun Y) : Prop :=
  ∀ (d : S.D), ∀ y ∈ Y.ys d, (G : S.D → Y.Yb → S.V) d y ∈ localization₂ w.asIdeal (S.Del d)

def Incl3Y {S₀ : GSD K} (Y : Cpl S) (w : HeightOneSpectrum (𝓞 K)) (t : K) (U : Module.End K (CplFun Y)) (k : S₀.EqFun →ₗ[K] CplFun Y) : Prop :=
  ∀ φ ∈ atW w S₀.intDel, CplInt Y w (t • U (k φ))

def TermInt1 {S₀ : GSD K} {Y : Cpl S} (k1 : S₀.D → S.D → Y.Yb → (S₀.V →ₗ[K] S.V)) (Uf : Module.End K (S.D → Y.Yb → S.V)) (w : HeightOneSpectrum (𝓞 K)) (t : K) : Prop :=
  ∀ (d₀ : S₀.D), ∀ x ∈ localization₂ w.asIdeal (S₀.Del d₀), ∀ (d : S.D), ∀ y ∈ Y.ys d,
    t • Uf (fun e y' => k1 d₀ e y' x) d y ∈ localization₂ w.asIdeal (S.Del d)

def TermInt2 (Y : Cpl S) {D₁ V₁ : Type} [AddCommGroup V₁] [Module K V₁] [Module (𝓞 K) V₁] (k2 : S.D → Y.Yb → D₁ → (S.V →ₗ[K] V₁))
    (Uf : Module.End K (D₁ → V₁)) (Rel : D₁ → Prop) (Del₁ : D₁ → Submodule (𝓞 K) V₁) (w : HeightOneSpectrum (𝓞 K)) (t : K) : Prop :=
  ∀ (d : S.D), ∀ y ∈ Y.ys d, ∀ x ∈ localization₂ w.asIdeal (S.Del d), ∀ e : D₁, Rel e → t • Uf (fun e' => k2 d y e' x) e ∈ localization₂ w.asIdeal (Del₁ e)

def Nbr.ofPerm (σ : Equiv.Perm S.D) (hσ : ∀ (g : S.G) (d : S.D), σ (g • d) = g • σ d) : Nbr S where
  up d := {σ d}
  dn d := {σ.symm d}
  mem_iff d d' := by
    rw [Finset.mem_singleton, Finset.mem_singleton, Equiv.eq_symm_apply]
    exact eq_comm
  equiv g d d' := by
    rw [Finset.mem_singleton, Finset.mem_singleton, hσ]
    exact smul_left_cancel_iff g

end Abs

section Pts

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

def upF (P : ST) (q : 𝓞 E) (p : DecoF E n ST SG Q) : Set (DecoF E n ST SG Q) :=
  {p' | p'.deco ∈ p.deco.upSet P q ∧ ∀ R : Q, p'.fr R = p.fr R}

def dnF (P : ST) (q : 𝓞 E) (p : DecoF E n ST SG Q) : Set (DecoF E n ST SG Q) :=
  {p' | p'.deco ∈ p.deco.dnSet P q ∧ ∀ R : Q, p'.fr R = p.fr R}

end Pts

section PtsFin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

omit [NumberField E] in

theorem decoF_ext {p p' : DecoF E n ST SG Q} (h1 : p.deco = p'.deco) (h2 : ∀ R : Q, p.fr R = p'.fr R) : p = p' :=
  Subtype.ext (Prod.ext h1 (funext h2))

theorem upF_finite (P : ST) (q : 𝓞 E) (p : DecoF E n ST SG Q) : (upF P q p).Finite := by
  refine Set.Finite.of_finite_image (f := DecoF.deco) ((DecoSet.upSet_finite p.deco P q).subset ?_) ?_
  · rintro _ ⟨p', hp', rfl⟩
    exact hp'.1
  · intro p1 h1 p2 h2 h
    exact decoF_ext h fun R => (h1.2 R).trans (h2.2 R).symm

theorem dnF_finite (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) (q : 𝓞 E) (p : DecoF E n ST SG Q) : (dnF P q p).Finite := by
  refine Set.Finite.of_finite_image (f := DecoF.deco) ((DecoSet.dnSet_finite p.deco P hne q).subset ?_) ?_
  · rintro _ ⟨p', hp', rfl⟩
    exact hp'.1
  · intro p1 h1 p2 h2 h
    exact decoF_ext h fun R => (h1.2 R).trans (h2.2 R).symm

theorem mem_upF_iff_mem_dnF {P : ST} (hP : MoveHyp ST SG P) {q : 𝓞 E} (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2)
    (p p' : DecoF E n ST SG Q) : p' ∈ upF P q p ↔ p ∈ dnF P q p' :=
  ⟨fun h => ⟨(DecoSet.mem_upSet_iff_mem_dnSet hP hq hq2 p.deco p'.deco).1 h.1, fun R => (h.2 R).symm⟩,
    fun h => ⟨(DecoSet.mem_upSet_iff_mem_dnSet hP hq hq2 p.deco p'.deco).2 h.1, fun R => (h.2 R).symm⟩⟩

theorem smul_mem_upF (a : UF E n × GLG E n SG × GLQ E n Q) (P : ST) (q : 𝓞 E) (p p' : DecoF E n ST SG Q) :
    a • p' ∈ upF P q (a • p) ↔ p' ∈ upF P q p := by
  have hd : ∀ r : DecoF E n ST SG Q, (a • r).deco = (a.1, a.2.1) • r.deco := fun _ => rfl
  have hf : ∀ (r : DecoF E n ST SG Q) (R : Q), (a • r).fr R = a.1.1 * r.fr R * ((a.2.2 R)⁻¹).1 := fun _ _ => rfl
  show ((a • p').deco ∈ (a • p).deco.upSet P q ∧ ∀ R : Q, (a • p').fr R = (a • p).fr R) ↔
    (p'.deco ∈ p.deco.upSet P q ∧ ∀ R : Q, p'.fr R = p.fr R)
  simp only [hd, hf]
  rw [DecoSet.smul_mem_upSet]
  simp only [mul_left_inj, mul_right_inj]

end PtsFin

section PtsG

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

def nbrF (C : CoefPk X n (DecoF X.E n ST SG Q)) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (P : ST) {q : 𝓞 X.E}
    (hP : MoveHyp ST SG P) (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) : Nbr (frmGSD C Λ Θ) where
  up p := (upF_finite P q p).toFinset
  dn p := (dnF_finite P hP.ne q p).toFinset
  mem_iff p p' := by
    rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    exact mem_upF_iff_mem_dnF hP hq hq2 p p'
  equiv g p p' := by
    rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    exact smul_mem_upF (FrmG.incl Λ Θ g) P q p p'

end PtsG

section ChN

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def nbrCh (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (j : ℕ) (b : L.β j) (P : Pr.vT u) : Nbr ((chF W sel mu L u j).mem b) :=
  nbrF (colValF W sel mu u j) (L.levG j b) (L.levQ j b) P (moveHyp_of_ok hPr u P) (T_unif hX hPr u P).1 (T_unif hX hPr u P).2

end ChN

section Local

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

def PhiStep (K : Type) [Field K] (P : ST) (q : 𝓞 E) (hne : conjPrime₂ P.1 ≠ P.1) (d : DecoSet E a ST SG) (d' : DecoSet E b ST SG') : Prop :=
  ∀ x : HomE E a b, ∑ e' ∈ (DecoSet.upSet_finite d' P q).toFinset, phiT K d.1 e'.1 x =
    ∑ e ∈ (DecoSet.dnSet_finite d P hne q).toFinset, phiT K e.1 d'.1 x

variable {K : Type} [Field K] {SB : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

def OffAdm (SB : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b))
    (ω : HomE E a b → K) : Prop :=
  (∀ x, ω x ≠ 0 → x ∈ divLat cA (homAt SB N N')) ∧ ∀ x y, y ∈ mulLat cB (homAt SB N N') → ω (x + y) = ω x

def ThMoveT (th : ThDist E K a b SB V V') (Sall : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ) (ST SG SG' : Finset (HeightOneSpectrum (𝓞 E)))
    (P : ST) (q : 𝓞 E) (c : K) : Prop :=
  ∀ (d d1 : DecoSet E a ST SG) (d' d1' : DecoSet E b ST SG') (fr : Frs E a SB) (fr' : Frs E b SB) (ω : HomE E a b → K),
    d1 ∈ d.upSet P q → d1' ∈ d'.upSet P q → OffAdm SB cA cB d.1.N d'.1.N ω →
      kerOf th Sall cA cB d1.1.N fr d1'.1.N fr' (fun x => phiT K d1.1 d1'.1 x * ω x) =
        c • kerOf th Sall cA cB d.1.N fr d'.1.N fr' (fun x => phiT K d1.1 d1'.1 x * ω x)

end Local

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

section Ops

variable (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)

def UCh (j : ℕ) (P : Pr.vT u) : Module.End X.K (chF W sel mu L u j).Forms :=
  famU fun b => nbrCh W sel mu L hX hPr u j b P

def UMid (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b) (P : Pr.vT u) :
    Module.End X.K (CplFun (ybCpl W sel mu cst L u m2 b hY)) :=
  (nbrCh W sel mu L hX hPr u (m2 + 1) b P).UY (ybCpl W sel mu cst L u m2 b hY)

end Ops

variable {u : Pr.Word}

def offEntry (i : ℕ) (al : L.β i) (be : L.β (i + 1)) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1))
    (x : HomE X.E (R.N i) (R.N (i + 1))) : X.K :=
  ∏ P : rowSG Pr sel mu, XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) (inFr (frsF sel mu p P) (frsF sel mu p' P) x)

def offCpl1 (m2 : ℕ) (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1))
    (Y : Set (Sp X.E (R.N (m2 + 1)))) (x : HomE X.E (R.N m2) (R.N (m2 + 1))) : X.K :=
  ∏ P : rowSG Pr sel mu, PsiAt Ch sel mu cst m2 P (L.h m2 al P) (inFr (frsF sel mu p₀ P) (frsF sel mu p P) x)
    ((frsF sel mu p P).symm (repY Y))

def offCpl2 (m2 : ℕ) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (d : RowPt Pr R sel mu)
    (x : HomE X.E (R.N (m2 + 1)) (R.N R.m)) : X.K :=
  ∏ P : rowSG Pr sel mu,
    PhiTop Ch mu cst.sharp m2 P.1 ((d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap ∘ₗ
        LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P ((((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap)
        ((frsF sel mu p P).symm (repY Y))

variable (R u) in

abbrev TopPt : Type := RowPt Pr R sel mu × DecoSet X.E (R.N R.m) (Pr.vT u) (rowSG Pr sel mu)

def tilTop (d : RowPt Pr R sel mu) : TopPt R sel mu u := (d, tilQ sel mu u d)

def TopRel (e : TopPt R sel mu u) : Prop :=
  ∀ w ∈ rowSG Pr sel mu, localization₂ w.asIdeal e.2.1.N = localization₂ w.asIdeal (tilQ sel mu u e.1).1.N

def XiCpl2X (m2 : ℕ) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (e : TopPt R sel mu u)
    (x : HomE X.E (R.N (m2 + 1)) (R.N R.m)) : X.K :=
  phiT X.K p.deco.1 e.2.1 x * offCpl2 Ch sel mu cst m2 p Y e.1 x

open Classical in

def cp2KX {m2 : ℕ} (T : ChTh W sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (e : TopPt R sel mu u) :
    (colValF W sel mu u (m2 + 1)).V →ₗ[X.K] (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).V :=
  if Y ∈ ybSet sel mu cst p.deco.1.N ∧ TopRel sel mu e then
    kerOf T.top (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (frsF sel mu p)
      e.2.1.N (frsT sel mu u e.1) (XiCpl2X Ch sel mu cst m2 p Y e)
  else 0

def upTop (P : Pr.vT u) (e : TopPt R sel mu u) : Finset (TopPt R sel mu u) :=
  (DecoSet.upSet_finite e.2 P (Pr.T u : 𝓞 X.E)).toFinset.map ⟨fun e' => (e.1, e'), fun _ _ h => (Prod.ext_iff.1 h).2⟩

def UTop (P : Pr.vT u) : Module.End X.K (TopPt R sel mu u → (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).V) :=
  upFun X.K _ (upTop sel mu P)

variable (R u) in

def heckeCommutationConst : X.K := (Pr.T u : X.K) ^ ((R.t + 1) / 2)

def PosT (u : Pr.Word) : Prop := ∀ P : Pr.vT u, MoveHyp (Pr.vT u) (rowSG Pr sel mu) P

def ThMoveCh {m2 : ℕ} (T : ChTh W sel mu u m2) : Prop :=
  Pr.Ok → R.m = m2 + 2 → (∀ i, i ≤ m2 → ∀ P : Pr.vT u, ThMoveT (T.th i) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (Pr.vT u) Pr.vGs Pr.vGs P
      (Pr.T u : 𝓞 X.E) (heckeCommutationConst R u)) ∧
    ∀ P : Pr.vT u, ThMoveT T.top (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (Pr.vT u) Pr.vGs (rowSG Pr sel mu) P
      (Pr.T u : 𝓞 X.E) (heckeCommutationConst R u)

def TopSuppAt (m2 : ℕ) : Prop :=
  ∀ (w : rowSG Pr sel mu) (y : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0)),
    PhiTop Ch mu cst.sharp m2 w.1 y ≠ 0 → ∀ s l, IntAt w.1 (y (Pi.single s 1) l)

def TopInvAt (m2 : ℕ) : Prop :=
  ∀ (w : rowSG Pr sel mu) (y z : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0)),
    (∀ s l, IntAt w.1 ((qOf w.1 : X.E)⁻¹ * z (Pi.single s 1) l)) →
      PhiTop Ch mu cst.sharp m2 w.1 (y + z) = PhiTop Ch mu cst.sharp m2 w.1 y

def OffAdmTop (u : Pr.Word) (m2 : ℕ) : Prop :=
  Pr.Ok → cst.Ok → R.m = m2 + 2 → (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) → PosT sel mu u → ∀ (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (d : RowPt Pr R sel mu), Y ∈ ybSet sel mu cst p.deco.1.N →
    OffAdm (rowSG Pr sel mu) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (tilQ sel mu u d).1.N (offCpl2 Ch sel mu cst m2 p Y d)

def Cp2XEquiv {m2 : ℕ} (T : ChTh W sel mu u m2) (b : L.β (m2 + 1)) : Prop :=
  ∀ (g : (midGSD W sel mu L u m2 b).G) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (e : TopPt R sel mu u),
    cp2KX W Ch sel mu cst T (g • p) ((fun v => g.1.1 v) '' Y) e = cp2KX W Ch sel mu cst T p Y e ∘ₗ (midGSD W sel mu L u m2 b).ρ g⁻¹

end Chain

section Stmts

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
  (hM : MatEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2)) (h1 : Cp1Equiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY)
  (hF : ∀ j, (chF W sel mu L u j).Ok)

open Classical in

def matKer : KerFam (chF W sel mu L u) := fun i al be =>
  if hi : i < m2 then ClsKer.mk (matK W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) i al be) (hM i hi al be) else zeroKer _ _

def KopM (i : ℕ) : (chF W sel mu L u i).Forms →ₗ[X.K] (chF W sel mu L u (i + 1)).Forms :=
  (matKer W Ch sel mu cst L A u m2 hM).step hF i

def Km1 (al : L.β m2) : ((chF W sel mu L u m2).mem al).EqFun →ₗ[X.K] CplFun (ybCpl W sel mu cst L u m2 b hY) :=
  cp1Op (S₀ := (chF W sel mu L u m2).mem al) (Y := ybCpl W sel mu cst L u m2 b hY) (cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) al) (h1 al)
    (hF m2 al) ((chF W sel mu L u m2).mem al).outSec

def KmStar : CplFun (ybCpl W sel mu cst L u m2 b hY) →ₗ[X.K] (TopPt R sel mu u → (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).V) :=
  cp2Fun (ybCpl W sel mu cst L u m2 b hY) (cp2KX W Ch sel mu cst (chTh W Ch sel mu cst A u m2)) (hF (m2 + 1) b)
    (midGSD W sel mu L u m2 b).outSec

def MatrixKernelHeckeCommutation : Prop :=
  ∀ i, i < m2 → ∀ P : Pr.vT u,
    CommF (UCh W sel mu L hX hPr u (i + 1) P) (KopM W Ch sel mu cst L A u m2 hM hF i) (UCh W sel mu L hX hPr u i P) (heckeCommutationConst R u)

def PenultimateHeckeCommutation : Prop :=
  ∀ (al : L.β m2) (P : Pr.vT u),
    CommC (UMid W sel mu cst L hX hPr u m2 b hY P) (Km1 W Ch sel mu cst L A u m2 b hY h1 hF al) (nbrCh W sel mu L hX hPr u m2 al P).U (heckeCommutationConst R u)

def CoupledSumHeckeCommutation : Prop :=
  ∀ P : Pr.vT u,
    CommC (UTop W sel mu P) (KmStar W Ch sel mu cst L A u m2 b hY hF) (UMid W sel mu cst L hX hPr u m2 b hY P) (heckeCommutationConst R u)

def UprodEnt (j : ℕ) (be : L.β j) (w : HeightOneSpectrum (𝓞 X.K)) : Module.End X.K ((chF W sel mu L u j).mem be).EqFun :=
  ((VVTc W u w).toList.map fun P => (nbrCh W sel mu L hX hPr u j be P).U).prod

def UprodFun (j : ℕ) (be : L.β j) (w : HeightOneSpectrum (𝓞 X.K)) :
    Module.End X.K (ChPt (R := R) sel mu u j → (colValF W sel mu u j).V) :=
  ((VVTc W u w).toList.map fun P => upFun X.K (colValF W sel mu u j).V (nbrCh W sel mu L hX hPr u j be P).up).prod

def UprodMid (w : HeightOneSpectrum (𝓞 X.K)) : Module.End X.K (CplFun (ybCpl W sel mu cst L u m2 b hY)) :=
  ((VVTc W u w).toList.map fun P => UMid W sel mu cst L hX hPr u m2 b hY P).prod

def UprodTop (w : HeightOneSpectrum (𝓞 X.K)) : Module.End X.K (TopPt R sel mu u → (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).V) :=
  ((VVTc W u w).toList.map fun P => UTop W sel mu P).prod

def MatrixKernelIntegralInclusion (w : HeightOneSpectrum (𝓞 X.K)) (e1 : ℕ) : Prop :=
  ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)),
    Incl3 w ((Pr.T u : X.K) ^ e1) (UprodEnt W sel mu L hX hPr u (i + 1) be w)
      ((matKer W Ch sel mu cst L A u m2 hM i al be).opOf (hF i al) ((chF W sel mu L u i).mem al).outSec)

def PenultimateKernelInclusion (w : HeightOneSpectrum (𝓞 X.K)) (e1 : ℕ) : Prop :=
  ∀ al : L.β m2, Incl3Y (ybCpl W sel mu cst L u m2 b hY) w ((Pr.T u : X.K) ^ e1) (UprodMid W sel mu cst L hX hPr u m2 b hY w)
    (Km1 W Ch sel mu cst L A u m2 b hY h1 hF al)

def CoupledSumIntegralInclusion (w : HeightOneSpectrum (𝓞 X.K)) (e1 : ℕ) : Prop :=
  ∀ G : CplFun (ybCpl W sel mu cst L u m2 b hY), CplInt (ybCpl W sel mu cst L u m2 b hY) w G → ∀ e : TopPt R sel mu u, TopRel sel mu e →
    ((Pr.T u : X.K) ^ e1) • UprodTop W sel mu u w (KmStar W Ch sel mu cst L A u m2 b hY hF G) e ∈
      localization₂ w.asIdeal ((colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).Del e.2)

def GamUnit (w : HeightOneSpectrum (𝓞 X.K)) : Prop :=
  ∀ (j : ℕ), j ≤ m2 + 1 → ∀ (be : L.β j) (c : ((chF W sel mu L u j).mem be).Cl),
    (((((chF W sel mu L u j).mem be).toCSDOf (hF j be) ((chF W sel mu L u j).mem be).outSec).wt c : ℕ) : 𝓞 X.K) ∉ w.asIdeal

def UKIntMat (w : HeightOneSpectrum (𝓞 X.K)) (e1 : ℕ) : Prop :=
  ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)) (p : ChPt (R := R) sel mu u i), ∀ x ∈ localization₂ w.asIdeal ((colValF W sel mu u i).Del p),
    ∀ p' : ChPt (R := R) sel mu u (i + 1),
      ((Pr.T u : X.K) ^ e1) • UprodFun W sel mu L hX hPr u (i + 1) be w
        (fun e' => matK W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) i al be p e' x) p' ∈ localization₂ w.asIdeal ((colValF W sel mu u (i + 1)).Del p')

def UprodMidFun (w : HeightOneSpectrum (𝓞 X.K)) :
    Module.End X.K ((midGSD W sel mu L u m2 b).D → (ybCpl W sel mu cst L u m2 b hY).Yb → (midGSD W sel mu L u m2 b).V) :=
  ((VVTc W u w).toList.map fun P => (nbrCh W sel mu L hX hPr u (m2 + 1) b P).UYfun (ybCpl W sel mu cst L u m2 b hY).Yb).prod

def UKIntCp1 (w : HeightOneSpectrum (𝓞 X.K)) (e1 : ℕ) : Prop :=
  ∀ al : L.β m2, TermInt1 (S₀ := (chF W sel mu L u m2).mem al) (Y := ybCpl W sel mu cst L u m2 b hY) (cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) al)
    (UprodMidFun W sel mu cst L hX hPr u m2 b hY w) w ((Pr.T u : X.K) ^ e1)

def UKIntCp2 (w : HeightOneSpectrum (𝓞 X.K)) (e1 : ℕ) : Prop :=
  TermInt2 (ybCpl W sel mu cst L u m2 b hY) (cp2KX W Ch sel mu cst (chTh W Ch sel mu cst A u m2)) (UprodTop W sel mu u w) (TopRel sel mu)
    (fun e => (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).Del e.2) w ((Pr.T u : X.K) ^ e1)

def RatK : Prop :=
  (∀ i, i ≤ m2 → A.JetsRat (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)) ∧
    A.JetsRat (R.N (m2 + 1)) (R.N R.m) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)

def TypeKM (Pl : LevFam X.E X.K R.r Pr.vGs) : Prop :=
  Cp2EquivOn W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY Pl

end Stmts

section Move

variable {X : Fields} (A : Amb X) {a b : ℕ}

def MuMoveT (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K) (a b : ℕ) (ST SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))) (P : ST) (q : 𝓞 X.E) : Prop :=
  ∀ (d d1 : DecoSet X.E a ST SG) (d' d1' : DecoSet X.E b ST SG') (fr : Frs X.E a SB) (fr' : Frs X.E b SB), d1 ∈ d.upSet P q → d1' ∈ d'.upSet P q →
    muInvDet sel SB mU mI d1.1.N fr * (muInvDet sel SB mU mI d1'.1.N fr')⁻¹ = muInvDet sel SB mU mI d.1.N fr * (muInvDet sel SB mU mI d'.1.N fr')⁻¹

def TabMoveT (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (a b : ℕ) (ST SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))) (P : ST) (q : 𝓞 X.E)
    (c : X.K) : Prop :=
  ∀ (d d1 : DecoSet X.E a ST SG) (d' d1' : DecoSet X.E b ST SG') (ω : HomE X.E a b → X.K), d1 ∈ d.upSet P q → d1' ∈ d'.upSet P q →
    OffAdm SB cA cB d.1.N d'.1.N ω → ∀ m : DVar X.Tau a b →₀ ℕ,
      A.tabK Sall cA cB d1.1.N d1'.1.N (fun x => phiT X.K d1.1 d1'.1 x * ω x) m =
        c * A.tabK Sall cA cB d.1.N d'.1.N (fun x => phiT X.K d1.1 d1'.1 x * ω x) m

end Move

section MoveCh

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def MuMoveCh (u : Pr.Word) (m2 : ℕ) : Prop :=
  (∀ i, i ≤ m2 → ∀ P : Pr.vT u, MuMoveT sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) (R.N i) (R.N (i + 1)) (Pr.vT u) Pr.vGs Pr.vGs P
      (Pr.T u : 𝓞 X.E)) ∧
    ∀ P : Pr.vT u, MuMoveT sel (rowSG Pr sel mu) (mUof Ch mu (m2 + 1)) (muAt Ch sel mu cst (m2 + 1)) (R.N (m2 + 1)) (R.N R.m) (Pr.vT u) Pr.vGs
      (rowSG Pr sel mu) P (Pr.T u : 𝓞 X.E)

def TabMoveCh (A : Amb X) (u : Pr.Word) (m2 : ℕ) : Prop :=
  Pr.Ok → R.m = m2 + 2 → (∀ i, i ≤ m2 → ∀ P : Pr.vT u, TabMoveT A (Sall sel mu u) (rowSG Pr sel mu) (cAof sel mu cst) (cBof sel mu cst u) (R.N i) (R.N (i + 1)) (Pr.vT u)
      Pr.vGs Pr.vGs P (Pr.T u : 𝓞 X.E) (heckeCommutationConst R u)) ∧
    ∀ P : Pr.vT u, TabMoveT A (Sall sel mu u) (rowSG Pr sel mu) (cAof sel mu cst) (cBof sel mu cst u) (R.N (m2 + 1)) (R.N R.m) (Pr.vT u)
      Pr.vGs (rowSG Pr sel mu) P (Pr.T u : 𝓞 X.E) (heckeCommutationConst R u)

end MoveCh

section MoveC

variable {X : Fields} (A : Amb X) {a b : ℕ}

def Amb.tabC (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (Ξ : HomE X.E a b → X.K) (m : DVar X.Tau a b →₀ ℕ) : ℂ :=
  latSum (divLat cA (homAt Sall N N')) (mulLat cB (homAt Sall N N')) fun x =>
    A.σ₀ (Ξ x) * ((A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' cB x) m)

def TabMoveC (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (a b : ℕ) (ST SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))) (P : ST) (q : 𝓞 X.E)
    (c : X.K) : Prop :=
  ∀ (d d1 : DecoSet X.E a ST SG) (d' d1' : DecoSet X.E b ST SG') (ω : HomE X.E a b → X.K), d1 ∈ d.upSet P q → d1' ∈ d'.upSet P q →
    OffAdm SB cA cB d.1.N d'.1.N ω → ∀ m : DVar X.Tau a b →₀ ℕ,
      A.tabC Sall cA cB d1.1.N d1'.1.N (fun x => phiT X.K d1.1 d1'.1 x * ω x) m =
        A.σ₀ c * A.tabC Sall cA cB d.1.N d'.1.N (fun x => phiT X.K d1.1 d1'.1 x * ω x) m

end MoveC

section MoveCCh

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def TabMoveCCh (A : Amb X) (u : Pr.Word) (m2 : ℕ) : Prop :=
  Pr.Ok → R.m = m2 + 2 → (∀ i, i ≤ m2 → ∀ P : Pr.vT u, TabMoveC A (Sall sel mu u) (rowSG Pr sel mu) (cAof sel mu cst) (cBof sel mu cst u) (R.N i) (R.N (i + 1)) (Pr.vT u)
      Pr.vGs Pr.vGs P (Pr.T u : 𝓞 X.E) (heckeCommutationConst R u)) ∧
    ∀ P : Pr.vT u, TabMoveC A (Sall sel mu u) (rowSG Pr sel mu) (cAof sel mu cst) (cBof sel mu cst u) (R.N (m2 + 1)) (R.N R.m) (Pr.vT u)
      Pr.vGs (rowSG Pr sel mu) P (Pr.T u : 𝓞 X.E) (heckeCommutationConst R u)

end MoveCCh

section OrdDet

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

def OrdDetUp (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (P : ST) (q : 𝓞 E) : Prop :=
  conjPrime₂ P.1 ≠ P.1 → ∀ d d1 : DecoSet E n ST SG, d1 ∈ d.upSet P q →
    ordDet P.1 d1.1.N = ordDet P.1 d.1.N - 1 ∧ ordDet (conjPrime₂ P.1) d1.1.N = ordDet (conjPrime₂ P.1) d.1.N + 1

def OrdDetFin : Prop :=
  ∀ N : Submodule (𝓞 E) (Sp E n), IsSdLat N → {Q : HeightOneSpectrum (𝓞 E) | ordDet Q N ≠ 0}.Finite

end OrdDet

section OrdDetCh

variable {X : Fields} {Pr : Primes X} (R : Ranks) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def OrdDetUpCh (u : Pr.Word) (m2 : ℕ) : Prop :=
  (∀ i, i ≤ m2 + 1 → ∀ P : Pr.vT u, OrdDetUp X.E (R.N i) (Pr.vT u) Pr.vGs P (Pr.T u : 𝓞 X.E)) ∧
    ∀ P : Pr.vT u, OrdDetUp X.E (R.N R.m) (Pr.vT u) (rowSG Pr sel mu) P (Pr.T u : 𝓞 X.E)

end OrdDetCh

section Dia

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

def diaF (c : DiaG E ST) (p : DecoF E n ST SG Q) : DecoF E n ST SG Q := ⟨(p.deco.dia c, p.1.2), p.2⟩

def diaPerm (c : DiaG E ST) : Equiv.Perm (DecoF E n ST SG Q) where
  toFun := diaF c
  invFun := diaF c⁻¹
  left_inv p := Subtype.ext (Prod.ext (DecoSet.dia_inv_dia c p.deco) rfl)
  right_inv p := Subtype.ext (Prod.ext (by
    have := DecoSet.dia_inv_dia c⁻¹ p.deco
    rwa [inv_inv] at this) rfl)

end Dia

section DiaCh

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
  (hM : MatEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2)) (h1 : Cp1Equiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY)
  (hF : ∀ j, (chF W sel mu L u j).Ok)

def nbrDia (j : ℕ) (be : L.β j) (c : DiaG X.E (Pr.vT u)) : Nbr ((chF W sel mu L u j).mem be) :=
  Nbr.ofPerm (S := (chF W sel mu L u j).mem be) (diaPerm c) fun _ _ => rfl

def diaTop (c : DiaG X.E (Pr.vT u)) (e : TopPt R sel mu u) : Finset (TopPt R sel mu u) := {(e.1, e.2.dia c)}

def MatrixKernelDiamondCommutation : Prop :=
  ∀ i, i < m2 → ∀ c : DiaG X.E (Pr.vT u),
    CommF (famU fun be => nbrDia W sel mu L u (i + 1) be c) (KopM W Ch sel mu cst L A u m2 hM hF i) (famU fun al => nbrDia W sel mu L u i al c) 1

def PenultimateDiamondCommutation : Prop :=
  ∀ (al : L.β m2) (c : DiaG X.E (Pr.vT u)),
    CommC ((nbrDia W sel mu L u (m2 + 1) b c).UY (ybCpl W sel mu cst L u m2 b hY)) (Km1 W Ch sel mu cst L A u m2 b hY h1 hF al)
      (nbrDia W sel mu L u m2 al c).U 1

def CoupledSumDiamondCommutation : Prop :=
  ∀ c : DiaG X.E (Pr.vT u),
    CommC (upFun X.K (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).V (diaTop sel mu u c)) (KmStar W Ch sel mu cst L A u m2 b hY hF)
      ((nbrDia W sel mu L u (m2 + 1) b c).UY (ybCpl W sel mu cst L u m2 b hY)) 1

end DiaCh

end Formalism.L2.Ker
