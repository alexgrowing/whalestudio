import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries

noncomputable section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Ws

theorem adicCont_map {Γ R R' : Type} [TopologicalSpace Γ] [CommRing R] [CommRing R'] (f : R →+* R') {I : Ideal R}
    {J : Ideal R'} (h : I ≤ J.comap f) {φ : Γ → R} (hφ : AdicCont I φ) : AdicCont J fun g => f (φ g) := by
  intro N
  have hN : I ^ N ≤ (J ^ N).comap f := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr h) N
  have := (hφ N).comp (Ideal.quotientMap (J ^ N) f hN)
  convert this using 1
  funext g
  simp [Ideal.quotientMap_mk]

variable {O Γ : Type} [CommRing O] [Group Γ]

@[ext] structure RD (Φ : Fr O Γ) (R : Type) [CommRing R] where
  r : Γ →* M4 R
  ψ : ∀ v, Fin 4 → Φ.Gv v →* R

def RD.map {Φ : Fr O Γ} {R R' : Type} [CommRing R] [CommRing R'] (D : RD Φ R) (f : R →+* R') : RD Φ R' :=
  ⟨mapRep f D.r, fun v i => f.toMonoidHom.comp (D.ψ v i)⟩

def Fr.splitRD (Φ : Fr O Γ) {R : Type} [CommRing R] (a : O →+* R) : RD Φ R :=
  ⟨mapRep a (diagRep Φ.χ), fun v i => (a.toMonoidHom.comp (Units.coeHom O)).comp ((Φ.χ i).comp (Φ.Gv v).subtype)⟩

structure Fr.IsRep (Φ : Fr O Γ) {R : Type} [CommRing R] (a : O →+* R) (r : Γ →* M4 R) : Prop where
  mult : ∀ g, IsGSp (a (Φ.ν g)) (r g)
  kill : ∀ g ∈ Φ.N, r g = 1
  nrm : (r Φ.g0).IsDiag

structure RD.Flags {Φ : Fr O Γ} {R : Type} [CommRing R] (D : RD Φ R) (n : Φ.ι → M4 R) : Prop where
  low : ∀ v, IsLow (n v)
  flag : ∀ v, ∀ s ∈ Φ.Gv v, IsUp (adj (n v) * D.r s * n v)
  char : ∀ v i (s : Φ.Gv v), (adj (n v) * D.r s * n v) i i = D.ψ v i s
  mu : ∀ v i (s : Φ.Gv v), (s : Γ) ∈ Φ.Mu v → D.ψ v i s = 1

variable [TopologicalSpace Γ] (Φ : Fr O Γ) {Λ : Type} [CommRing Λ] [IsLocalRing Λ] (a : O →+* Λ)

structure Fr.Near (τ : ℤ × ℤ →+ ℤ) {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (D : RD Φ R) : Prop where
  rep : Φ.IsRep ((algebraMap Λ R).comp a) D.r
  cont : ∀ i j, AdicCont (maximalIdeal R) fun g => D.r g i j
  contψ : ∀ v i, AdicCont (maximalIdeal R) fun s => D.ψ v i s
  diag : ∀ g i, res Λ R (D.r g i i) = residue Λ (a (Φ.χ i g))
  off : ∀ g i j, i ≠ j → τ (wt i j) ≤ 0 → D.r g i j ∈ maximalIdeal R
  redψ : ∀ v i (s : Φ.Gv v), res Λ R (D.ψ v i s) = residue Λ (a (Φ.χ i s))

def Fr.RUniv {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (D : RD Φ R) : Prop :=
  Φ.Near a 0 D ∧ ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (D' : RD Φ R'), Φ.Near a 0 D' →
    ∃! f : R →ₐ[Λ] R', D.map (f : R →+* R') = D'

variable {Φ} in

structure RD.Graded {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (D : RD Φ R) (W : WPres Λ (ℤ × ℤ) R) : Prop where
  max : ∀ s, W.z s ∈ maximalIdeal R
  ent : ∀ g i j, D.r g i j ∈ W.part (wt i j)
  chr : ∀ v i s, D.ψ v i s ∈ W.part 0
  var : ∀ s, (∃ g i j, ∃ c : Λ, W.z s = D.r g i j - algebraMap Λ R c ∧ W.wt s = wt i j ∧ (i ≠ j → c = 0)) ∨
    ∃ v i t, ∃ c : Λ, W.z s = D.ψ v i t - algebraMap Λ R c ∧ W.wt s = 0

structure Core where
  A : Type
  [cA : CommRing A]
  [aA : Algebra Λ A]
  B : Type
  [cB : CommRing B]
  [aB : Algebra Λ B]
  [coB : IsCO Λ B]
  [aBA : Algebra B A]
  [tower : IsScalarTower Λ B A]
  ft : Algebra.FiniteType B A
  D : RD Φ A
  rep : Φ.IsRep ((algebraMap Λ A).comp a) D.r
  cont : ∀ i j, AdicCont ((maximalIdeal B).map (algebraMap B A)) fun g => D.r g i j
  gen : Algebra.adjoin B (Set.range fun x : Γ × Fin 4 × Fin 4 => D.r x.1 x.2.1 x.2.2) = ⊤
  cp : Γ → B[X]
  cp_map : ∀ g, (cp g).map (algebraMap B A) = (D.r g).charpoly
  cp_cont : ∀ n, AdicCont (maximalIdeal B) fun g => (cp g).coeff n
  cp_red : ∀ g, (cp g).map (res Λ B : B →+* ResidueField Λ) = ∏ i, (X - C (residue Λ (a (Φ.χ i g))))
  ψ : ∀ v, Fin 4 → Φ.Gv v → B
  ψ_map : ∀ v i s, algebraMap B A (ψ v i s) = D.ψ v i s
  ψ_cont : ∀ v i, AdicCont (maximalIdeal B) (ψ v i)
  ψ_red : ∀ v i (s : Φ.Gv v), res Λ B (ψ v i s) = residue Λ (a (Φ.χ i s))
  genB : ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (f f' : B →ₐ[Λ] R),
    (∀ g n, f ((cp g).coeff n) = f' ((cp g).coeff n)) → (∀ v i s, f (ψ v i s) = f' (ψ v i s)) → f = f'
  univ : ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (τ : ℤ × ℤ →+ ℤ) (D' : RD Φ R), Φ.Near a τ D' →
    ∃ f : A →ₐ[Λ] R, D.map (f : A →+* R) = D'

attribute [instance] Core.cA Core.aA Core.cB Core.aB Core.coB Core.aBA Core.tower

structure Pre where
  A : Type
  [cA : CommRing A]
  [aA : Algebra Λ A]
  B : Type
  [cB : CommRing B]
  [aB : Algebra Λ B]
  [coB : IsCO Λ B]
  [aBA : Algebra B A]
  [tower : IsScalarTower Λ B A]
  ft : Algebra.FiniteType B A
  P : PD Φ.ι Γ A
  pair : Φ.IsPair ((algebraMap Λ A).comp a) P
  cont : P.Cont ((maximalIdeal B).map (algebraMap B A))
  gen : Algebra.adjoin B ((Set.range fun x : Γ × Fin 4 × Fin 4 => P.r x.1 x.2.1 x.2.2) ∪
    Set.range fun x : Φ.ι × Fin 4 × Fin 4 => P.n x.1 x.2.1 x.2.2) = ⊤
  cp : Γ → B[X]
  cp_map : ∀ g, (cp g).map (algebraMap B A) = (P.r g).charpoly
  cp_cont : ∀ n, AdicCont (maximalIdeal B) fun g => (cp g).coeff n
  cp_red : ∀ g, (cp g).map (res Λ B : B →+* ResidueField Λ) = ∏ i, (X - C (residue Λ (a (Φ.χ i g))))
  ψ : Φ.ι → Fin 4 → Γ → B
  ψ_map : ∀ v i, ∀ s ∈ Φ.Gv v, algebraMap B A (ψ v i s) = P.ψ v i s
  ψ_cont : ∀ v i, AdicCont (maximalIdeal B) fun s : Φ.Gv v => ψ v i s
  ψ_red : ∀ v i, ∀ s ∈ Φ.Gv v, res Λ B (ψ v i s) = residue Λ (a (Φ.χ i s))
  genB : ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (f f' : B →ₐ[Λ] R),
    (∀ g n, f ((cp g).coeff n) = f' ((cp g).coeff n)) → (∀ v i, ∀ s ∈ Φ.Gv v, f (ψ v i s) = f' (ψ v i s)) → f = f'
  univ : ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (c : PD Φ.ι Γ (ResidueField Λ)) (Q : PD Φ.ι Γ R),
    Φ.IsRes ((residue Λ).comp a) c → Φ.Lifts a c Q → ∃ f : A →ₐ[Λ] R, P.map (f : A →+* R) = Q

attribute [instance] Pre.cA Pre.aA Pre.cB Pre.aB Pre.coB Pre.aBA Pre.tower

variable {Φ a}

def Pre.Line (Y : Pre Φ a) : Prop :=
  ∀ Q : PD Φ.ι Γ (ResidueField Λ)[X], Φ.IsRes (C.comp ((residue Λ).comp a)) Q →
    ∃ f : Y.A →ₐ[Λ] (ResidueField Λ)[X], Y.P.map (f : Y.A →+* (ResidueField Λ)[X]) = Q ∧
      ∀ b ∈ maximalIdeal Y.B, f (algebraMap Y.B Y.A b) = 0

def Pre.toSpace (Y : Pre Φ a) (h : Function.Injective (algebraMap Y.B Y.A)) (hl : Y.Line) : Space Φ a :=
  { A := Y.A, B := Y.B, inj := h, ft := Y.ft, P := Y.P, pair := Y.pair, cont := Y.cont, gen := Y.gen, cp := Y.cp,
    cp_map := Y.cp_map, cp_cont := Y.cp_cont, cp_red := Y.cp_red, ψ := Y.ψ, ψ_map := Y.ψ_map, ψ_cont := Y.ψ_cont,
    ψ_red := Y.ψ_red, genB := Y.genB, univ := Y.univ, line := hl }

variable (Λ) in

structure Laur {R S : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] [CommRing S] [Algebra Λ S] [IsCO Λ S] (c : ℕ)
    (e : S →+* LaurentSeries R) : Prop where
  inj : Function.Injective e
  alg : ∀ x : Λ, e (algebraMap Λ S x) = HahnSeries.single 0 (algebraMap Λ R x)
  mem : ∀ (n : ℤ) (x : R), 0 < n ∨ (-(c : ℤ) ≤ n ∧ x ∈ maximalIdeal R) → ∃ y ∈ maximalIdeal S, e y = HahnSeries.single n x
  small : ∀ n : ℤ, ∃ M : ℕ, ∀ y ∈ maximalIdeal S ^ M, (e y).coeff n = 0

end UpperTheory.V.Ws

end
